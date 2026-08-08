local graph = require("main.analysis.graph")
local regs = require("main.analysis.registers")

local ssa = {}

local function copy(source)
    local out = {}; for k, v in pairs(source) do out[k] = v end; return out
end
local function same(a, b)
    for k, v in pairs(a) do if b[k] ~= v then return false end end
    for k, v in pairs(b) do if a[k] ~= v then return false end end
    return true
end
local function seteq(a, b)
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end


local ambig = {}


local function packflow(proto, cfg, check)
    local pin, pout, before, consumer = {}, {}, {}, {}
    local changed, iterations = true, 0
    local limit = math.max(64, (#cfg.blocks + 1) * 256)

    local function merge(block)
        if block.id == 1 or #block.predecessors == 0 then return nil end
        local first, have = nil, false
        for _, pred in ipairs(block.predecessors) do
            local v = pout[pred]
            if not have then first, have = v, true
            elseif first ~= v then return ambig end
        end
        return first
    end

    while changed do
        if check then check() end
        iterations += 1
        if iterations > limit then error("LumenV4: ValuePack dataflow failed to converge", 2) end
        changed = false
        for _, block in ipairs(cfg.blocks) do
            local incoming = merge(block)
            if pin[block.id] ~= incoming then pin[block.id] = incoming; changed = true end
            local cur = incoming
            for _, pc in ipairs(block.pcs) do
                local _, _, pack = regs.readWrite(proto.Instructions[pc])
                if pack.consumesTop then consumer[pc] = cur end
                if pack.producesTop then
                    cur = pc
                elseif pack.consumesTop then
                    cur = nil
                end
            end
            if pout[block.id] ~= cur then pout[block.id] = cur; changed = true end
        end
    end


    for _, block in ipairs(cfg.blocks) do
        local cur = pin[block.id]
        for _, pc in ipairs(block.pcs) do
            before[pc] = cur
            local _, _, pack = regs.readWrite(proto.Instructions[pc])
            if pack.consumesTop then consumer[pc] = cur end
            if pack.producesTop then cur = pc elseif pack.consumesTop then cur = nil end
        end
    end
    return pin, pout, before, consumer, ambig
end

local function liveness(proto, cfg, packinput, ambiguous, check)
    local use, def, lin, lout = {}, {}, {}, {}
    for _, b in ipairs(cfg.blocks) do
        local u, d = {}, {}
        for _, pc in ipairs(b.pcs) do
            local r, w, pack = regs.readWrite(proto.Instructions[pc])
            for reg in pairs(r) do if not d[reg] then u[reg] = true end end
            if pack.openReadFrom then
                local producer = packinput[pc]
                if type(producer) == "number" then
                    local _, _, pp = regs.readWrite(proto.Instructions[producer])
                    local topbase = pp.openWriteFrom
                    if topbase and topbase >= pack.openReadFrom then
                        for reg = pack.openReadFrom, topbase - 1 do if not d[reg] then u[reg] = true end end
                    end
                end
            end
            for reg in pairs(w) do d[reg] = true end
            if pack.openWriteFrom then for reg = pack.openWriteFrom, 254 do d[reg] = true end end
        end
        use[b.id], def[b.id], lin[b.id], lout[b.id] = u, d, {}, {}
    end

    local changed = true
    local iterations = 0
    local limit = math.max(64, #cfg.blocks * 512)
    while changed do
        if check then check() end
        iterations += 1
        if iterations > limit then error("LumenV4: liveness failed to converge", 2) end
        changed = false
        for i = #cfg.blocks, 1, -1 do
            local b = cfg.blocks[i]
            local out = {}
            for _, sid in ipairs(b.successors) do for r in pairs(lin[sid]) do out[r] = true end end
            local inn = copy(use[b.id])
            for r in pairs(out) do if not def[b.id][r] then inn[r] = true end end
            if not seteq(lout[b.id], out) then lout[b.id] = out; changed = true end
            if not seteq(lin[b.id], inn) then lin[b.id] = inn; changed = true end
        end
    end
    local after = {}
    for _, b in ipairs(cfg.blocks) do
        local live = copy(lout[b.id])
        for i = #b.pcs, 1, -1 do
            local pc = b.pcs[i]
            after[pc] = copy(live)
            local r, w, pack = regs.readWrite(proto.Instructions[pc])
            if pack.openWriteFrom then
                for reg = pack.openWriteFrom, 254 do live[reg] = nil end
            end
            for reg in pairs(w) do live[reg] = nil end
            if pack.openReadFrom then
                local producer = packinput[pc]
                if type(producer) == "number" then
                    local _, _, pp = regs.readWrite(proto.Instructions[producer])
                    local topbase = pp.openWriteFrom
                    if topbase and topbase >= pack.openReadFrom then
                        for reg = pack.openReadFrom, topbase - 1 do live[reg] = true end
                    end
                end
            end
            for reg in pairs(r) do live[reg] = true end
        end
    end
    return lin, lout, after
end

function ssa.build(proto, cfg, check, limits)
    cfg = cfg or graph.build(proto, check, limits)
    local packinblock, packoutblock, packbefore, packinput, ambiguouspack = packflow(proto, cfg, check)
    local livein, liveout, liveafter = liveness(proto, cfg, packinput, ambiguouspack, check)
    local result = {
        proto = proto, cfg = cfg, params = {}, defsByPC = {}, usesByPC = {}, versions = {}, phisByBlock = {},
        inVersions = {}, outVersions = {}, useCount = {}, defUse = {}, undefByReg = {}, packsByPC = {},
        liveIn = livein, liveOut = liveout, liveAfter = liveafter,
        packInBlock = packinblock, packOutBlock = packoutblock, packBefore = packbefore,
        packInput = packinput, ambiguousPack = ambiguouspack,
    }
    local nextver = 1
    local function newver(kind, reg, pc, block)
        local id = nextver; nextver += 1
        result.versions[id] = { id = id, kind = kind, reg = reg, pc = pc, block = block }
        return id
    end
    local function undef(reg)
        local id = result.undefByReg[reg]
        if not id then id = newver("undef", reg, nil, nil); result.undefByReg[reg] = id end
        return id
    end

    for reg = 0, (proto.ParameterCount or 0) - 1 do
        local id = newver("param", reg, 0, 1); result.params[reg] = id
    end


    for _, b in ipairs(cfg.blocks) do
        if check then check() end
        for _, pc in ipairs(b.pcs) do
            local _, writes, pack = regs.readWrite(proto.Instructions[pc])
            result.packsByPC[pc] = next(pack) and pack or nil
            local need = next(writes) ~= nil or pack.openWriteFrom ~= nil
            if need then
                local defs = {}; result.defsByPC[pc] = defs
                for reg in pairs(writes) do defs[reg] = newver("def", reg, pc, b.id) end
                if pack.openWriteFrom then
                    for reg in pairs(liveafter[pc] or {}) do
                        if reg >= pack.openWriteFrom and not defs[reg] then defs[reg] = newver("pack", reg, pc, b.id) end
                    end
                end
            end
        end
    end

    local phimap = {}
    local function getphi(blockid, reg)
        local m = phimap[blockid]; if not m then m = {}; phimap[blockid] = m end
        if m[reg] then return m[reg] end
        local id = newver("phi", reg, nil, blockid); m[reg] = id
        local p = result.phisByBlock[blockid]; if not p then p = {}; result.phisByBlock[blockid] = p end
        p[reg] = { id = id, reg = reg, inputs = {}, incoming = {}, missing = false }
        return id
    end

    local function merge(block)
        if block.id == 1 then return copy(result.params) end
        if #block.predecessors == 0 then return {} end
        local merged = {}
        for reg in pairs(livein[block.id] or {}) do
            local unique, incoming, count = {}, {}, 0
            local prior = phimap[block.id] and phimap[block.id][reg]
            for _, pred in ipairs(block.predecessors) do
                local version = (result.outVersions[pred] or {})[reg] or undef(reg)
                incoming[pred] = version
                if version ~= prior and not unique[version] then unique[version] = true; count += 1 end
            end
            if count == 1 then
                for v in pairs(unique) do merged[reg] = v break end
            elseif count > 1 then
                local id = getphi(block.id, reg); merged[reg] = id
                local rec = result.phisByBlock[block.id][reg]
                rec.inputs, rec.incoming = unique, incoming
                rec.missing = unique[undef(reg)] == true
            end
        end
        return merged
    end

    local changed, iterations = true, 0
    local limit = math.max(128, (#cfg.blocks + 1) * 1024)
    while changed do
        if check then check() end
        iterations += 1
        if iterations > limit then error("LumenV4: SSA failed to converge", 2) end
        changed = false
        for _, b in ipairs(cfg.blocks) do
            local incoming = merge(b)
            if not same(result.inVersions[b.id] or {}, incoming) then result.inVersions[b.id] = incoming; changed = true end
            local current = copy(incoming)
            for _, pc in ipairs(b.pcs) do
                local defs = result.defsByPC[pc]
                if defs then for reg, v in pairs(defs) do current[reg] = v end end
            end
            if not same(result.outVersions[b.id] or {}, current) then result.outVersions[b.id] = current; changed = true end
        end
    end
    result.converged, result.iterations = true, iterations

    for bid, phis in pairs(result.phisByBlock) do
        local incoming = result.inVersions[bid] or {}
        for reg, p in pairs(phis) do
            if incoming[reg] ~= p.id then phis[reg] = nil; result.versions[p.id].dead = true end
        end
        if not next(phis) then result.phisByBlock[bid] = nil end
    end


    for _, b in ipairs(cfg.blocks) do
        local current = copy(result.inVersions[b.id] or {})
        for _, pc in ipairs(b.pcs) do
            local reads = regs.readWrite(proto.Instructions[pc])
            local uses = {}
            for reg in pairs(reads) do
                local version = current[reg] or undef(reg)
                uses[reg] = version
                result.useCount[version] = (result.useCount[version] or 0) + 1
                local list = result.defUse[version] or {}; result.defUse[version] = list
                list[#list + 1] = { pc = pc, reg = reg, block = b.id }
            end
            if next(uses) then result.usesByPC[pc] = uses end
            local defs = result.defsByPC[pc]
            if defs then for reg, v in pairs(defs) do current[reg] = v end end
        end
    end

    for bid, phis in pairs(result.phisByBlock) do
        local predcount = #cfg.blocks[bid].predecessors
        for reg, p in pairs(phis) do
            local n = 0
            for _, pred in ipairs(cfg.blocks[bid].predecessors) do
                local v = assert(p.incoming[pred], "LumenV4: phi missing predecessor input")
                n += 1
                result.useCount[v] = (result.useCount[v] or 0) + 1
                local list = result.defUse[v] or {}; result.defUse[v] = list
                list[#list + 1] = { phi = p.id, block = bid, reg = reg, predecessor = pred }
            end
            assert(n == predcount, "LumenV4: phi predecessor cardinality mismatch")
        end
    end

    local function verifyssa()
        local function dominates(defv, useblock, usepc)
            if not defv or defv.kind == "undef" then return true end
            if defv.kind == "param" then return cfg.dominators[useblock] and cfg.dominators[useblock][1] == true end
            if defv.kind == "phi" then return cfg.dominators[useblock] and cfg.dominators[useblock][defv.block] == true end
            if defv.block == useblock then return type(defv.pc) == "number" and defv.pc < usepc end
            return cfg.dominators[useblock] and cfg.dominators[useblock][defv.block] == true
        end

        for pc, uses in pairs(result.usesByPC) do
            local blockid = assert(cfg.blockmap[pc], "LumenV4: SSA use outside reachable CFG")
            for reg, version in pairs(uses) do
                local v = assert(result.versions[version], "LumenV4: SSA use has invalid version")
                assert(dominates(v, blockid, pc), ("LumenV4: SSA definition v%d does not dominate use r%d@pc%d"):format(version, reg, pc))
            end
        end

        for bid, phis in pairs(result.phisByBlock) do
            local block = assert(cfg.blocks[bid])
            for reg, phi in pairs(phis) do
                local seen = 0
                for _, pred in ipairs(block.predecessors) do
                    local expected = (result.outVersions[pred] or {})[reg] or undef(reg)
                    assert(phi.incoming[pred] == expected, ("LumenV4: phi v%d has invalid edge value from b%d"):format(phi.id, pred))
                    seen += 1
                end
                assert(seen == #block.predecessors, "LumenV4: phi edge cardinality mismatch")
            end
        end

        for pc, pack in pairs(result.packsByPC) do
            if pack and pack.consumesTop then
                local producer = result.packInput[pc]
                if producer ~= result.ambiguousPack then
                    if type(producer) ~= "number" then
                        error("LumenV4: UNSUPPORTED open ValuePack consumer has no reaching producer at pc " .. tostring(pc), 2)
                    end
                    local pp = result.packsByPC[producer]
                    assert(pp and pp.producesTop, "LumenV4: ValuePack consumer references non-producer")
                end
            end
        end
        return true
    end
    result.verified = verifyssa()

    function result:versionForUse(pc, reg) local u = self.usesByPC[pc]; return u and u[reg] or nil end
    function result:versionForDef(pc, reg) local d = self.defsByPC[pc]; return d and d[reg] or nil end
    function result:isSingleUse(v) return (self.useCount[v] or 0) == 1 end
    function result:onlyUse(v) local u = self.defUse[v]; return u and #u == 1 and u[1] or nil end
    function result:summary()
        local phis, versions, undefs, packs, divergentpacks = 0, 0, 0, 0, 0
        for _, ps in pairs(self.phisByBlock) do for _ in pairs(ps) do phis += 1 end end
        for _, v in ipairs(self.versions) do if not v.dead then versions += 1; if v.kind == "undef" then undefs += 1 end end end
        for pc, p in pairs(self.packsByPC) do
            if p then
                packs += 1
                if p.consumesTop and self.packInput[pc] == self.ambiguousPack then divergentpacks += 1 end
            end
        end
        return { converged = true, iterations = self.iterations, versions = versions, phis = phis, blocks = #self.cfg.blocks, undefs = undefs, openPacks = packs, divergentPacks = divergentpacks }
    end
    return result
end

return ssa
