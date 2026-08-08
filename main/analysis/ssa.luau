local graph = require("main.analysis.graph")
local regs = require("main.analysis.registers")

local ssa = {}

local function copy(source)
    local result = {}
    for key, value in pairs(source) do
        result[key] = value
    end
    return result
end

local function same(a, b)
    for key, value in pairs(a) do
        if b[key] ~= value then
            return false
        end
    end

    for key, value in pairs(b) do
        if a[key] ~= value then
            return false
        end
    end

    return true
end

function ssa.build(proto, cfg)
    cfg = cfg or graph.build(proto)

    local result = {
        proto = proto,
        cfg = cfg,
        params = {},
        defsByPC = {},
        usesByPC = {},
        versions = {},
        phisByBlock = {},
        inVersions = {},
        outVersions = {},
        useCount = {},
        defUse = {},
    }

    local nextver = 1

    local function newver(kind, reg, pc, block)
        local id = nextver
        nextver = nextver + 1

        result.versions[id] = {
            id = id,
            kind = kind,
            reg = reg,
            pc = pc,
            block = block,
        }

        return id
    end

    for reg = 0, (proto.ParameterCount or 0) - 1 do
        local id = newver("param", reg, 0, 1)
        result.params[reg] = id
    end

    for _, block in ipairs(cfg.blocks) do
        for _, pc in ipairs(block.pcs) do
            local op = proto.Instructions[pc]
            local pair = cfg.rw and cfg.rw[pc]
            local writes = pair and pair.writes or select(2, regs.readWrite(op))

            if next(writes) then
                local defs = {}
                result.defsByPC[pc] = defs

                for reg in pairs(writes) do
                    defs[reg] = newver("def", reg, pc, block.id)
                end
            end
        end
    end

    local phimap = {}

    local function getphi(blockId, reg)
        local byRegister = phimap[blockId]
        if not byRegister then
            byRegister = {}
            phimap[blockId] = byRegister
        end

        local id = byRegister[reg]
        if id then
            return id
        end

        id = newver("phi", reg, nil, blockId)
        byRegister[reg] = id

        local blockPhis = result.phisByBlock[blockId]
        if not blockPhis then
            blockPhis = {}
            result.phisByBlock[blockId] = blockPhis
        end

        blockPhis[reg] = {
            id = id,
            reg = reg,
            inputs = {},
        }

        return id
    end

    local function merge(block)
        if block.id == 1 then
            return copy(result.params)
        end

        if #block.predecessors == 0 then
            return {}
        end

        local regs = {}
        for _, pred in ipairs(block.predecessors) do
            local vals = result.outVersions[pred] or {}
            for reg in pairs(vals) do
                regs[reg] = true
            end
        end

        local merged = {}

        for reg in pairs(regs) do
            local unique = {}
            local count = 0
            local byreg = phimap[block.id]
            local prior = byreg and byreg[reg]

            local missing = false
            for _, pred in ipairs(block.predecessors) do
                local vals = result.outVersions[pred] or {}
                local version = vals[reg]

                if version == nil then
                    missing = true
                elseif version ~= prior and not unique[version] then
                    unique[version] = true
                    count = count + 1
                end
            end

            if missing then count = count + 1 end

            if count == 1 then
                for version in pairs(unique) do
                    merged[reg] = version
                    break
                end
            elseif count > 1 then
                local phi = getphi(block.id, reg)
                merged[reg] = phi

                local record = result.phisByBlock[block.id][reg]
                record.inputs = unique
                record.missing = missing
            end
        end

        return merged
    end

    local queue = {}
    local queued = {}
    local head = 1
    local iterations = 0
    local maxiter = math.max(64, #cfg.blocks * 64)

    local function push(id)
        if not queued[id] then
            queued[id] = true
            queue[#queue + 1] = id
        end
    end

    for _, block in ipairs(cfg.blocks) do push(block.id) end

    while head <= #queue and iterations < maxiter do
        local id = queue[head]
        head += 1
        queued[id] = nil
        iterations += 1

        local block = cfg.blocks[id]
        local incoming = merge(block)
        local oldin = result.inVersions[id] or {}
        local inchg = not same(oldin, incoming)

        if inchg or result.inVersions[id] == nil then
            result.inVersions[id] = incoming
        end

        local current = copy(incoming)

        for _, pc in ipairs(block.pcs) do
            local defs = result.defsByPC[pc]
            if defs then
                for reg, version in pairs(defs) do
                    current[reg] = version
                end
            end
        end

        local oldout = result.outVersions[id] or {}
        if not same(oldout, current) or result.outVersions[id] == nil then
            result.outVersions[id] = current
            for _, sid in ipairs(block.successors) do push(sid) end
        end
    end

    result.converged = head > #queue
    result.iterations = iterations

    for blockId, phis in pairs(result.phisByBlock) do
        local incoming = result.inVersions[blockId] or {}
        for reg, phi in pairs(phis) do
            if incoming[reg] ~= phi.id then
                phis[reg] = nil
                result.versions[phi.id].dead = true
            end
        end
        if not next(phis) then result.phisByBlock[blockId] = nil end
    end

    for _, block in ipairs(cfg.blocks) do
        local current = copy(result.inVersions[block.id] or {})

        for _, pc in ipairs(block.pcs) do
            local op = proto.Instructions[pc]
            local pair = cfg.rw and cfg.rw[pc]
            local reads = pair and pair.reads or select(1, regs.readWrite(op))
            local uses = {}

            for reg in pairs(reads) do
                local version = current[reg]
                if version ~= nil then
                    uses[reg] = version
                    result.useCount[version] = (result.useCount[version] or 0) + 1

                    local uses = result.defUse[version]
                    if not uses then
                        uses = {}
                        result.defUse[version] = uses
                    end

                    uses[#uses + 1] = {
                        pc = pc,
                        reg = reg,
                        block = block.id,
                    }
                end
            end

            if next(uses) then
                result.usesByPC[pc] = uses
            end

            local defs = result.defsByPC[pc]
            if defs then
                for reg, version in pairs(defs) do
                    current[reg] = version
                end
            end
        end
    end

    for blockId, phis in pairs(result.phisByBlock) do
        for reg, phi in pairs(phis) do
            for version in pairs(phi.inputs) do
                result.useCount[version] = (result.useCount[version] or 0) + 1

                local uses = result.defUse[version]
                if not uses then
                    uses = {}
                    result.defUse[version] = uses
                end

                uses[#uses + 1] = {
                    phi = phi.id,
                    block = blockId,
                    reg = reg,
                }
            end
        end
    end

    function result:versionForUse(pc, reg)
        local uses = self.usesByPC[pc]
        return uses and uses[reg] or nil
    end

    function result:versionForDef(pc, reg)
        local defs = self.defsByPC[pc]
        return defs and defs[reg] or nil
    end

    function result:isSingleUse(version)
        return (self.useCount[version] or 0) == 1
    end

    function result:onlyUse(version)
        local uses = self.defUse[version]
        return uses and #uses == 1 and uses[1] or nil
    end

    function result:summary()
        local phiCount = 0
        for _, phis in pairs(self.phisByBlock) do
            for _ in pairs(phis) do
                phiCount = phiCount + 1
            end
        end

        local versions = 0
        for _, ver in ipairs(self.versions) do if not ver.dead then versions = versions + 1 end end
        return {
            converged = self.converged,
            iterations = self.iterations,
            versions = versions,
            phis = phiCount,
            blocks = #self.cfg.blocks,
        }
    end

    return result
end

return ssa