assert(type(loadstring) == "function", "LumenDecomp requires loadstring()")

local mod = {
    ["main.analysis.dominators"] = [===[
local dom = {}

local function equal(a, b)
    for key in pairs(a) do if not b[key] then return false end end
    for key in pairs(b) do if not a[key] then return false end end
    return true
end

function dom.compute(blocks)
    local all = {}
    for _, block in ipairs(blocks) do all[block.id] = true end

    local out = {}
    for _, block in ipairs(blocks) do
        local set = {}

        if block.id == 1 then
            set[1] = true
        else
            for id in pairs(all) do set[id] = true end
        end

        out[block.id] = set
    end

    local chg = true
    while chg do
        chg = false

        for _, block in ipairs(blocks) do
            if block.id ~= 1 then
                local set = nil

                for _, pred in ipairs(block.predecessors) do
                    local predSet = out[pred]

                    if set == nil then
                        set = {}
                        for id in pairs(predSet) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not predSet[id] then set[id] = nil end
                        end
                    end
                end

                set = set or {}
                set[block.id] = true

                if not equal(out[block.id], set) then
                    out[block.id] = set
                    chg = true
                end
            end
        end
    end

    return out
end

return dom
]===],
    ["main.analysis.graph"] = [===[
local ins = require("main.bytecode.instructions")
local regs = require("main.analysis.registers")
local dom = require("main.analysis.dominators")
local loops = require("main.analysis.loops")
local post = require("main.analysis.postdom")

local graph = {}

function graph.build(proto)
    local ops = proto.Instructions
    local aux = ins.auxSlots(proto)
    local leaders = { [1] = true }
    local nexts = {}

    local function valid(pc)
        return pc >= 1 and pc <= #ops and not aux[pc]
    end

    for pc = 1, #ops do
        if not aux[pc] then
            local op = ops[pc]
            local name = ins.name(op)
            local nextPC = ins.next(proto, pc, aux)
            local successors = {}

            if name == "RETURN" then

            elseif name == "LOADB" and (op.C or 0) ~= 0 then
                local target = pc + op.C + 1
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            elseif ins.isConditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then successors[#successors + 1] = nextPC; leaders[nextPC] = true end

            elseif ins.isUnconditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            else
                if valid(nextPC) then successors[#successors + 1] = nextPC end
            end

            nexts[pc] = successors
        end
    end

    local list = {}
    for pc in pairs(leaders) do if valid(pc) then list[#list + 1] = pc end end
    table.sort(list)

    local blocks = {}
    local blockmap = {}

    for index, startPC in ipairs(list) do
        local nextLeader = list[index + 1] or (#ops + 1)
        local pcs = {}

        for pc = startPC, nextLeader - 1 do
            if not aux[pc] then
                pcs[#pcs + 1] = pc
                blockmap[pc] = index
            end
        end

        blocks[index] = {
            id = index,
            startPC = startPC,
            endPC = pcs[#pcs] or startPC,
            pcs = pcs,
            successors = {},
            predecessors = {},
        }
    end

    for _, block in ipairs(blocks) do
        local seen = {}
        for _, nextpc in ipairs(nexts[block.endPC] or {}) do
            local nextblock = blockmap[nextpc]
            if nextblock and not seen[nextblock] then
                seen[nextblock] = true
                block.successors[#block.successors + 1] = nextblock
            end
        end
    end

    for _, block in ipairs(blocks) do
        for _, successor in ipairs(block.successors) do
            blocks[successor].predecessors[#blocks[successor].predecessors + 1] = block.id
        end
    end

    local dominators = dom.compute(blocks)
    local postdom, ipdom = post.run(blocks)

    return {
        proto = proto,
        aux = aux,
        blocks = blocks,
        blockmap = blockmap,
        nexts = nexts,
        dominators = dominators,
        postdom = postdom,
        ipdom = ipdom,
        loops = loops.find(blocks, dominators),
        registerStats = regs.stats(proto, aux),
    }
end

return graph
]===],
    ["main.analysis.loops"] = [===[
local loops = {}

function loops.find(blocks, dom)
    local out = {}

    for _, latch in ipairs(blocks) do
        for _, hid in ipairs(latch.successors) do
            if dom[latch.id] and dom[latch.id][hid] then
                local set = { [hid] = true, [latch.id] = true }
                local todo = { latch.id }
                local n = 1

                while n <= #todo do
                    local id = todo[n]
                    n += 1
                    for _, pid in ipairs(blocks[id].predecessors) do
                        if not set[pid] then
                            set[pid] = true
                            if pid ~= hid then todo[#todo + 1] = pid end
                        end
                    end
                end

                local exits = {}
                local seen = {}
                for id in pairs(set) do
                    for _, sid in ipairs(blocks[id].successors) do
                        if not set[sid] and not seen[sid] then
                            seen[sid] = true
                            exits[#exits + 1] = blocks[sid].startPC
                        end
                    end
                end
                table.sort(exits)

                out[#out + 1] = {
                    header = hid,
                    latch = latch.id,
                    headerPC = blocks[hid].startPC,
                    latchPC = latch.endPC,
                    nodes = set,
                    exits = exits,
                    exitPC = #exits == 1 and exits[1] or nil,
                }
            end
        end
    end

    return out
end

return loops
]===],
    ["main.analysis.postdom"] = [===[
local post = {}

local function same(a, b)
    for k in pairs(a) do
        if not b[k] then return false end
    end
    for k in pairs(b) do
        if not a[k] then return false end
    end
    return true
end

function post.run(blocks)
    local all = {}
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = {}
    for _, b in ipairs(blocks) do
        local set = {}
        if #b.successors == 0 then
            set[b.id] = true
        else
            for id in pairs(all) do set[id] = true end
        end
        pd[b.id] = set
    end

    local dirty = true
    while dirty do
        dirty = false
        for i = #blocks, 1, -1 do
            local b = blocks[i]
            if #b.successors > 0 then
                local set
                for _, sid in ipairs(b.successors) do
                    local src = pd[sid]
                    if not set then
                        set = {}
                        for id in pairs(src) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not src[id] then set[id] = nil end
                        end
                    end
                end
                set = set or {}
                set[b.id] = true
                if not same(pd[b.id], set) then
                    pd[b.id] = set
                    dirty = true
                end
            end
        end
    end

    local ip = {}
    for _, b in ipairs(blocks) do
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        for _, id in ipairs(cand) do
            local near = true
            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    near = false
                    break
                end
            end
            if near then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip
end

return post
]===],
    ["main.analysis.registers"] = [===[
local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then
        set[value] = true
    end
end

local function range(set, first, last)
    for reg = first, last do
        add(set, reg)
    end
end

function regs.readWrite(op)
    local reads, writes = {}, {}
    local name = ins.name(op)
    local A, B, C = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL"
        or name == "GETIMPORT" or name == "NEWTABLE" or name == "DUPTABLE"
        or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, A)

    elseif name == "MOVE" then
        add(reads, B); add(writes, A)

    elseif name == "SETGLOBAL" or name == "SETUPVAL" then
        add(reads, A)

    elseif name == "GETTABLE" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "SETTABLE" then
        add(reads, A); add(reads, B); add(reads, C)

    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then
        add(reads, B); add(writes, A)

    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then
        add(reads, A); add(reads, B)

    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        add(reads, B); add(writes, A); add(writes, A + 1)

    elseif name == "CALL" or name == "CALLFB" then
        if B == 0 then add(reads, A) else range(reads, A, A + B - 1) end
        if C == 0 then add(writes, A) elseif C > 1 then range(writes, A, A + C - 2) end

    elseif name == "RETURN" then
        if B == 0 then add(reads, A) elseif B > 1 then range(reads, A, A + B - 2) end

    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV"
        or name == "MOD" or name == "POW" or name == "IDIV"
        or name == "AND" or name == "OR" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK"
        or name == "MODK" or name == "POWK" or name == "IDIVK"
        or name == "ANDK" or name == "ORK" then
        add(reads, B); add(writes, A)

    elseif name == "SUBRK" or name == "DIVRK" then
        add(reads, C); add(writes, A)

    elseif name == "CONCAT" then
        range(reads, B, C); add(writes, A)

    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
        add(reads, B); add(writes, A)

    elseif name == "SETLIST" then
        add(reads, A)
        if C == 0 then add(reads, B) elseif C > 1 then range(reads, B, B + C - 2) end

    elseif name == "FORNPREP" or name == "FORNLOOP" then
        range(reads, A, A + 3); range(writes, A + 2, A + 3)

    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, A, A + 2)

    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, A, A + 2); add(writes, A + 2)
        if count > 0 then range(writes, A + 3, A + 2 + count) end

    elseif name == "GETVARARGS" then
        if B == 0 then add(writes, A) elseif B > 1 then range(writes, A, A + B - 2) end

    elseif name == "CAPTURE" then
        if A == 0 or A == 1 then add(reads, B) end

    elseif name == "JUMPIF" or name == "JUMPIFNOT"
        or name == "JUMPXEQKNIL" or name == "JUMPXEQKB"
        or name == "JUMPXEQKN" or name == "JUMPXEQKS"
        or name == "CMPPROTO" then
        add(reads, A)

    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ"
        or name == "JUMPIFLT" or name == "JUMPIFLE"
        or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, A); add(reads, bit32.band(aux, 0xff))

    elseif name == "NEWCLASSMEMBER" then
        add(reads, A); add(reads, C)

    elseif name == "NEWCLASS" then
        if B ~= 0xff then add(reads, B) end
        add(writes, A)
    end

    return reads, writes
end

function regs.stats(proto, aux)
    local stats = {}
    aux = aux or ins.auxSlots(proto)

    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = {
                reads = 0, writes = 0,
                firstWrite = nil, lastWrite = nil,
                firstRead = nil, lastRead = nil,
                firstAccess = nil, lastAccess = nil,
            }
            stats[reg] = entry
        end
        return entry
    end

    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local op = proto.Instructions[pc]
            local reads, writes = regs.readWrite(op)

            for reg in pairs(reads) do
                local entry = get(reg)
                entry.reads += 1
                entry.firstRead = entry.firstRead or pc
                entry.lastRead = pc
                entry.firstAccess = entry.firstAccess or pc
                entry.lastAccess = pc
            end

            local name = ins.name(op)
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local entry = get(reg)
                    entry.writes += 1
                    entry.firstWrite = entry.firstWrite or pc
                    entry.lastWrite = pc
                    entry.firstAccess = entry.firstAccess or pc
                    entry.lastAccess = pc
                end
            end
        end
    end

    return stats
end

return regs
]===],
    ["main.analysis.ssa"] = [===[
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
            local _, writes = regs.readWrite(op)

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

    local changed = true
    local iterations = 0
    local maxiter = math.max(16, #cfg.blocks * 8)

    while changed and iterations < maxiter do
        iterations = iterations + 1
        changed = false

        for _, block in ipairs(cfg.blocks) do
            local incoming = merge(block)
            local oldin = result.inVersions[block.id] or {}

            if not same(oldin, incoming) then
                result.inVersions[block.id] = incoming
                changed = true
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

            local oldout = result.outVersions[block.id] or {}
            if not same(oldout, current) then
                result.outVersions[block.id] = current
                changed = true
            end
        end
    end

    result.converged = not changed
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
            local reads, _ = regs.readWrite(op)
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
]===],
    ["main.api"] = [===[
local ver = require("main.version")
local cfg = require("main.config")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")
local dis = require("main.diagnostics.disassembler")
local view = require("main.diagnostics.inspect")
local env = require("main.runtime.environment")
local save = require("main.serialization.save")
local dump = require("main.dump")

local api = {
    Version = ver.version,
    Name = ver.name,
}

local function parsebc(raw, opt)
    return iri.get():Deserialize(raw, opt.iridium)
end

function api:parseBytecode(raw, opt)
    return parsebc(raw, cfg(opt))
end

function api:parse(obj, opt)
    return self:parseBytecode(bc.fromScript(obj), opt)
end

function api:decompileBytecode(raw, opt)
    opt = cfg(opt)

    local parsed = parsebc(raw, opt)
    local d = decomp.new(opt)
    local source, details = d:decompileParsed(parsed)

    return source, {
        version = ver.version,
        bytecodeVersion = parsed.BytecodeVersion,
        typesVersion = parsed.TypesVersion,
        protoCount = parsed.ProtoCount,
        hasRobloxEnvelope = parsed.HasRobloxEnvelope,
        robloxTrailerVersion = parsed.RobloxTrailerVersion,
        details = details,
    }
end

function api:decompile(obj, opt)
    return self:decompileBytecode(bc.fromScript(obj), opt)
end

function api:tryDecompile(obj, opt)
    local ok, source, metadata = pcall(function()
        local text, meta = self:decompile(obj, opt)
        return text, meta
    end)

    if ok then
        return { success = true, source = source, metadata = metadata }
    end

    return { success = false, error = tostring(source) }
end

function api:disassemble(obj, opt)
    local parsed = self:parse(obj, opt)
    local proto = assert(parsed.Protos[parsed.ProtoEntryPoint])
    return dis.proto(proto), parsed
end

function api:inspectGraph(obj, opt)
    return view.graph(self:parse(obj, opt))
end

function api:inspectSSA(obj, opt)
    return view.ssa(self:parse(obj, opt))
end

function api:inspectIR(obj, opt)
    opt = cfg(opt)
    return view.ir(self:parse(obj, opt), opt)
end

function api:dependencyInfo()
    return iri.info()
end

function api:save(obj, file, opt)
    return save.run(self, obj, file, opt)
end

function api:dump(opt)
    return dump.run(self, opt)
end

function api:auto(opt)
    return dump.auto(self, opt)
end

function api:serializerInfo()
    return save.info()
end

function api:installGlobal(name)
    name = name or "lumendecompile"
    local e = env.get()

    e[name] = function(obj, opt)
        local source = self:decompile(obj, opt)
        return source
    end

    return name
end

function api:installAsDecompiler()
    local e = env.get()
    local previous = rawget(e, "decompile")

    e.decompile = function(obj, opt)
        local source = self:decompile(obj, opt)
        return source
    end

    return previous
end

return api
]===],
    ["main.ast.booleans"] = [===[
local pass = {}

local function val(n)
    if not n or n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) or v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function neg(s)
    local x = s:match("^not%s+%((.*)%)$") or s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        local done = false
        if cur and cur.kind == "if" and #cur.branches == 1 and not cur.elsebody and nxt and nxt.kind == "return" then
            local body = cur.branches[1].body
            if #body.body == 1 then
                local a = val(body.body[1])
                local b = val(nxt)
                if a and b then
                    local x
                    if a == "true" and b == "false" then x = cur.branches[1].cond
                    elseif a == "false" and b == "true" then x = neg(cur.branches[1].cond)
                    elseif a == b then x = a
                    else x = "if " .. cur.branches[1].cond .. " then " .. a .. " else " .. b end
                    out[#out + 1] = { kind = "return", text = "return " .. x }
                    i += 2
                    done = true
                end
            end
        end
        if not done then
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.callbacks"] = [===[
local pass = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hits(s, name)
    local n = 0
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local at = 1
    while true do
        local a, b = s:find(pat, at)
        if not a then break end
        n += 1
        at = b + 1
    end
    return n
end

local function count(node, name)
    if not node or node.dead then return 0 end
    local n = 0
    if node.text then n += hits(node.text, name) end
    if node.cond then n += hits(node.cond, name) end
    if node.head then n += hits(node.head, name) end
    if node.args then n += hits(node.args, name) end
    if node.kind == "if" then
        for _, b in ipairs(node.branches) do
            n += hits(b.cond, name)
            for _, x in ipairs(b.body.body) do n += count(x, name) end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body) do n += count(x, name) end end
    elseif node.body then
        for _, x in ipairs(node.body.body) do n += count(x, name) end
    end
    return n
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
end

local function split(text, name)
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local a, b = text:find(pat)
    if not a then return nil end
    if text:find(pat, b + 1) then return nil end
    local pre = text:sub(1, a - 1)
    if not pre:find("%(") then return nil end
    return pre, text:sub(b + 1)
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        if cur and cur.kind == "function" and cur.localfn and nxt and nxt.kind == "raw"
            and count(cur, cur.name) == 0 and rest(block.body, i + 1, cur.name) == 1 then
            local pre, post = split(nxt.text, cur.name)
            if pre then
                out[#out + 1] = { kind = "callback", pre = pre, post = post, args = cur.args, body = cur.body }
                i += 2
            else
                out[#out + 1] = cur
                i += 1
            end
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.compound"] = [===[
local pass = {}

local list = {
    { "//", "//=" }, { "..", "..=" }, { "+", "+=" }, { "-", "-=" },
    { "*", "*=" }, { "/", "/=" }, { "%", "%=" }, { "^", "^=" },
}

local function pesc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function one(s)
    local name, rhs = s:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if not name then return s end
    local pre = "^" .. pesc(name) .. "%s*"
    for _, x in ipairs(list) do
        local tail = rhs:match(pre .. pesc(x[1]) .. "%s*(.+)$")
        if tail and tail ~= "" then return name .. " " .. x[2] .. " " .. tail end
    end
    return s
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "raw" then node.text = one(node.text)
        elseif node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.conditions"] = [===[
local pass = {}

local function same(a, b)
    if a == b then return true end
    if type(a) ~= type(b) or type(a) ~= "table" then return false end
    for k, v in pairs(a) do
        if k ~= "dead" and not same(v, b[k]) then return false end
    end
    for k, v in pairs(b) do
        if k ~= "dead" and a[k] == nil and v ~= nil then return false end
    end
    return true
end

local function merge(node)
    local out = {}
    for _, b in ipairs(node.branches) do
        local prev = out[#out]
        if prev and same(prev.body, b.body) then
            prev.cond = "(" .. prev.cond .. ") or (" .. b.cond .. ")"
        else
            out[#out + 1] = b
        end
    end
    node.branches = out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do
                walk(branch.body)
                local body = branch.body.body
                if #body == 1 and body[1].kind == "if" and not body[1].elsebody and #body[1].branches == 1 then
                    local sub = body[1]
                    branch.cond = "(" .. branch.cond .. ") and (" .. sub.branches[1].cond .. ")"
                    branch.body = sub.branches[1].body
                end
            end
            if node.elsebody then walk(node.elsebody) end
            merge(node)
        elseif node.body then
            walk(node.body)
        end
    end

end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.deadcode"] = [===[
local pass = {}

local function walk(block)
    local out = {}
    local done = false
    for _, node in ipairs(block.body) do
        if not node.dead and not done then
            if node.kind == "if" then
                for _, branch in ipairs(node.branches) do walk(branch.body) end
                if node.elsebody then walk(node.elsebody) end
            elseif node.body then
                walk(node.body)
            end
            out[#out + 1] = node
            if node.kind == "return" or node.kind == "break" or node.kind == "continue" then done = true end
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.fold"] = [===[
local pass = {}

local function bool(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    if s == "true" then return true end
    if s == "false" or s == "nil" then return false end
    if s == "not true" then return false end
    if s == "not false" or s == "not nil" then return true end
    return nil
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            local keep = {}
            local done = false
            for _, b in ipairs(node.branches) do
                local v = bool(b.cond)
                if v == true then
                    if #keep == 0 then
                        for _, sub in ipairs(b.body.body) do out[#out + 1] = sub end
                    else
                        node.branches = keep
                        node.elsebody = b.body
                        out[#out + 1] = node
                    end
                    done = true
                    break
                elseif v == nil then
                    keep[#keep + 1] = b
                end
            end
            if not done then
                if #keep == 0 then
                    if node.elsebody then
                        for _, sub in ipairs(node.elsebody.body) do out[#out + 1] = sub end
                    end
                else
                    node.branches = keep
                    out[#out + 1] = node
                end
            end
        elseif node.kind == "while" then
            walk(node.body)
            if bool(node.cond) ~= false then out[#out + 1] = node end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.guards2"] = [===[
local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local cmp = { " ~= ", " == ", " <= ", " >= ", " < ", " > " }

local function neg(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    for _, mid in ipairs(cmp) do
        local p = s:find(mid, 1, true)
        if p then
            local op = mid:sub(2, -2)
            local a = s:sub(1, p - 1)
            local b = s:sub(p + #mid)
            return a .. " " .. inv[op] .. " " .. b
        end
    end
    local x = s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
end

local function term(b)
    local x = b and b.body and b.body[#b.body]
    return x and (x.kind == "return" or x.kind == "break" or x.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.elsebody) and not term(node.branches[1].body) then
                out[#out + 1] = {
                    kind = "if",
                    branches = { { cond = neg(node.branches[1].cond), body = node.elsebody } },
                    elsebody = nil,
                }
                for _, x in ipairs(node.branches[1].body.body) do out[#out + 1] = x end
            else
                out[#out + 1] = node
            end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.inline"] = [===[
local pass = {}

local function init(n)
    if not n or n.kind ~= "raw" then return nil end
    local a, b = n.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+%s*=%s*(.+)$")
    if a then return a, b end
    return n.text:match("^local%s+([%a_][%w_]*)%s*=%s*(.+)$")
end

local function simple(s)
    if s == "..." or s:find("%(") then return false end
    return true
end

local function word(s, name)
    local n = 0
    for x in s:gmatch("[%a_][%w_]*") do
        if x == name then n += 1 end
    end
    return n
end

local function count(n, name)
    if not n or n.dead then return 0 end
    local out = 0
    if n.text then out += word(n.text, name) end
    if n.cond then out += word(n.cond, name) end
    if n.head then out += word(n.head, name) end
    if n.args then out += word(n.args, name) end
    if n.kind == "if" then
        for _, b in ipairs(n.branches) do
            out += word(b.cond, name)
            for _, x in ipairs(b.body.body) do out += count(x, name) end
        end
        if n.elsebody then for _, x in ipairs(n.elsebody.body) do out += count(x, name) end end
    elseif n.body then
        for _, x in ipairs(n.body.body) do out += count(x, name) end
    end
    return out
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        local name, rhs = init(cur)
        local used = name and rest(block.body, i + 1, name) or 0
        if name and nxt and used == 1 and simple(rhs) and nxt.kind == "return" and nxt.text == "return " .. name then
            out[#out + 1] = { kind = "return", text = "return " .. rhs }
            i += 2
        elseif name and nxt and used == 1 and simple(rhs) and nxt.kind == "if" and #nxt.branches > 0 then
            local c = nxt.branches[1].cond
            if c == name then
                nxt.branches[1].cond = rhs
                out[#out + 1] = nxt
                i += 2
            elseif c == "not " .. name or c == "not (" .. name .. ")" then
                nxt.branches[1].cond = "not (" .. rhs .. ")"
                out[#out + 1] = nxt
                i += 2
            else
                out[#out + 1] = cur
                i += 1
            end
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.locals"] = [===[
local pass = {}

local function walk(block)
    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end

        local nextn = block.body[i + 1]
        if node.kind == "raw" and nextn and nextn.kind == "raw" then
            local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
            if name then
                local lhs, rhs = nextn.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
                if lhs == name then
                    node.text = node.text .. " = " .. rhs
                    i += 1
                end
            end
        end
        out[#out + 1] = node
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.logic"] = [===[
local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function neg(s)
    s = trim(s)
    local x = s:match("^not%s+%((.+)%)$") or s:match("^not%s+(.+)$")
    if not x then return s end
    x = trim(x)
    local y = x:match("^not%s+%((.+)%)$") or x:match("^not%s+([%a_][%w_%.]*)$")
    if y then return trim(y) end
    for _, op in ipairs({ "~=", "==", "<=", ">=", "<", ">" }) do
        local a, b = x:match("^(.-)%s+" .. op:gsub("([^%w])", "%%%1") .. "%s+(.+)$")
        if a and b then return trim(a) .. " " .. inv[op] .. " " .. trim(b) end
    end
    return s
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do
                x.cond = neg(x.cond)
                walk(x.body)
            end
            if n.elsebody then walk(n.elsebody) end
        elseif n.kind == "while" or n.kind == "repeat" then
            n.cond = neg(n.cond)
            walk(n.body)
        elseif n.body then
            walk(n.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.lower"] = [===[
local n = require("main.ast.nodes")

local build = {}
build.__index = build

local function add(body, node)
    body.body[#body.body + 1] = node
    return node
end

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

function build.new()
    local root = n.block()
    return setmetatable({ root = root, stack = { { kind = "root", body = root } } }, build)
end

function build:body()
    return self.stack[#self.stack].body
end

function build:add(node)
    return add(self:body(), node)
end

function build:last()
    local body = self:body().body
    return body[#body]
end

function build:emit(line)
    line = trim(line)

    local cond, act = line:match("^if%s+(.+)%s+then%s+(break)%s+end$")
    if not cond then cond, act = line:match("^if%s+(.+)%s+then%s+(continue)%s+end$") end
    if cond then
        local node = n.if_(cond)
        add(node.branches[1].body, n.term(act, act))
        return self:add(node)
    end

    cond = line:match("^if%s+(.+)%s+then$")
    if cond then
        local node = self:add(n.if_(cond))
        self.stack[#self.stack + 1] = { kind = "if", node = node, body = node.branches[1].body }
        return node
    end

    cond = line:match("^elseif%s+(.+)%s+then$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray elseif")
        local branch = { cond = cond, body = n.block() }
        top.node.branches[#top.node.branches + 1] = branch
        top.body = branch.body
        return top.node
    end

    if line == "else" then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray else")
        top.node.elsebody = n.block()
        top.body = top.node.elsebody
        return top.node
    end

    cond = line:match("^while%s+(.+)%s+do$")
    if cond then
        local node = self:add(n.while_(cond))
        self.stack[#self.stack + 1] = { kind = "while", node = node, body = node.body }
        return node
    end

    if line == "repeat" then
        local node = self:add(n.repeat_())
        self.stack[#self.stack + 1] = { kind = "repeat", node = node, body = node.body }
        return node
    end

    cond = line:match("^until%s+(.+)$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "repeat", "LumenDecomp: stray until")
        top.node.cond = cond
        self.stack[#self.stack] = nil
        return top.node
    end

    local head = line:match("^(for%s+.+)%s+do$")
    if head then
        local node = self:add(n.for_(head))
        self.stack[#self.stack + 1] = { kind = "for", node = node, body = node.body }
        return node
    end

    if line == "do" then
        local node = self:add(n.do_())
        self.stack[#self.stack + 1] = { kind = "do", node = node, body = node.body }
        return node
    end

    local name, args = line:match("^local%s+function%s+([%w_]+)%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), true, false))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    name, args = line:match("^([%w_]+)%s*=%s*function%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), false, true))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    if line == "end" then
        local top = self.stack[#self.stack]
        assert(#self.stack > 1 and top.kind ~= "repeat", "LumenDecomp: stray end")
        self.stack[#self.stack] = nil
        return top.node
    end

    if line == "break" then return self:add(n.term("break", line)) end
    if line == "continue" then return self:add(n.term("continue", line)) end
    if line == "return" or line:match("^return%s") then return self:add(n.term("return", line)) end

    return self:add(n.raw(line))
end

function build:done()
    assert(#self.stack == 1, "LumenDecomp: AST builder has unclosed blocks")
    return self.root
end

return build
]===],
    ["main.ast.nodes"] = [===[
local n = {}

function n.block()
    return { kind = "block", body = {} }
end

function n.raw(s)
    return { kind = "raw", text = s }
end

function n.if_(cond)
    return { kind = "if", branches = { { cond = cond, body = n.block() } }, elsebody = nil }
end

function n.while_(cond)
    return { kind = "while", cond = cond, body = n.block() }
end

function n.repeat_()
    return { kind = "repeat", cond = "true", body = n.block() }
end

function n.for_(head)
    return { kind = "for", head = head, body = n.block() }
end

function n.do_()
    return { kind = "do", body = n.block() }
end

function n.func(name, args, body, localfn, assign)
    return { kind = "function", name = name, args = args, body = body or n.block(), localfn = localfn == true, assign = assign == true }
end

function n.term(kind, text)
    return { kind = kind, text = text }
end

return n
]===],
    ["main.ast.pipeline"] = [===[
local fold = require("main.ast.fold")
local cond = require("main.ast.conditions")
local logic = require("main.ast.logic")
local guards = require("main.recover.guards")
local guards2 = require("main.ast.guards2")
local selectp = require("main.ast.selects")
local ret = require("main.ast.returns")
local inline = require("main.ast.inline")
local callbacks = require("main.ast.callbacks")
local bools = require("main.ast.booleans")
local comp = require("main.ast.compound")
local locals = require("main.ast.locals")
local dead = require("main.ast.deadcode")

local pass = {}

function pass.run(root, opt)
    opt = opt or {}
    if opt.dce ~= false then dead.run(root) end
    if opt.fold ~= false then fold.run(root) end
    if opt.conditions ~= false then cond.run(root) end
    if opt.selects ~= false then selectp.run(root) end
    if opt.returns ~= false then ret.run(root) end
    if opt.inlineast ~= false then inline.run(root) end
    if opt.callbacks ~= false then callbacks.run(root) end
    if opt.booleans ~= false then bools.run(root) end
    if opt.guards ~= false then
        guards2.run(root)
        guards.run(root)
    end
    locals.run(root)
    if opt.compound ~= false then comp.run(root) end
    logic.run(root)
    if opt.conditions ~= false then cond.run(root) end
    if opt.dce ~= false then dead.run(root) end
    return root
end

return pass
]===],
    ["main.ast.printer"] = [===[
local printast = {}

local function line(out, depth, s)
    out[#out + 1] = string.rep("    ", depth) .. s
end

local function block(out, b, depth)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, depth, node.text)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, depth, (i == 1 and "if " or "elseif ") .. branch.cond .. " then")
                    block(out, branch.body, depth + 1)
                end
                if node.elsebody then
                    line(out, depth, "else")
                    block(out, node.elsebody, depth + 1)
                end
                line(out, depth, "end")
            elseif k == "while" then
                line(out, depth, "while " .. node.cond .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "repeat" then
                line(out, depth, "repeat")
                block(out, node.body, depth + 1)
                line(out, depth, "until " .. node.cond)
            elseif k == "for" then
                line(out, depth, node.head .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "do" then
                line(out, depth, "do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "callback" then
                line(out, depth, node.pre .. "function(" .. node.args .. ")")
                block(out, node.body, depth + 1)
                line(out, depth, "end" .. node.post)
            elseif k == "function" then
                if node.localfn then
                    line(out, depth, "local function " .. node.name .. "(" .. node.args .. ")")
                elseif node.assign then
                    line(out, depth, node.name .. " = function(" .. node.args .. ")")
                else
                    line(out, depth, "function " .. node.name .. "(" .. node.args .. ")")
                end
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            end
        end
    end
end

function printast.run(root)
    local out = {}
    block(out, root, 0)
    return table.concat(out, "\n")
end

return printast
]===],
    ["main.ast.returns"] = [===[
local pass = {}

local function ret(b)
    if not b or #b.body ~= 1 then return nil end
    local n = b.body[1]
    if n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) then return nil end
    if v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function expr(n)
    if n.kind ~= "if" or not n.elsebody or #n.branches == 0 then return nil end
    local vals = {}
    for _, b in ipairs(n.branches) do
        local v = ret(b.body)
        if not v then return nil end
        vals[#vals + 1] = { cond = b.cond, val = v }
    end
    local last = ret(n.elsebody)
    if not last then return nil end
    if #vals == 1 then
        if vals[1].val == last then return vals[1].val end
        if vals[1].val == "true" and last == "false" then return vals[1].cond end
        if vals[1].val == "false" and last == "true" then return "not (" .. vals[1].cond .. ")" end
    end
    local out = "if " .. vals[1].cond .. " then " .. vals[1].val
    for i = 2, #vals do out = out .. " elseif " .. vals[i].cond .. " then " .. vals[i].val end
    return out .. " else " .. last
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do walk(x.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end
    local out = {}
    for _, n in ipairs(b.body) do
        local x = expr(n)
        if x then out[#out + 1] = { kind = "return", text = "return " .. x }
        else out[#out + 1] = n end
    end
    b.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.selects"] = [===[
local pass = {}

local function asn(node)
    if not node or node.kind ~= "raw" then return nil end
    local a, b = node.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if a then return a, b end
end

local function decl(node)
    if not node or node.kind ~= "raw" then return nil end
    local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
    return name, name and node.text or nil
end

local function pick(node)
    if node.kind ~= "if" or not node.elsebody or #node.branches == 0 then return nil end
    local name
    local parts = {}
    for _, b in ipairs(node.branches) do
        if #b.body.body ~= 1 then return nil end
        local n, v = asn(b.body.body[1])
        if not n or (name and name ~= n) then return nil end
        name = n
        parts[#parts + 1] = { cond = b.cond, val = v }
    end
    if #node.elsebody.body ~= 1 then return nil end
    local n, v = asn(node.elsebody.body[1])
    if not n or n ~= name then return nil end
    if #parts == 1 then
        if parts[1].val == v then return name, v end
        if parts[1].val == "true" and v == "false" then return name, parts[1].cond end
        if parts[1].val == "false" and v == "true" then return name, "not (" .. parts[1].cond .. ")" end
    end
    local out = "if " .. parts[1].cond .. " then " .. parts[1].val
    for i = 2, #parts do out = out .. " elseif " .. parts[i].cond .. " then " .. parts[i].val end
    out = out .. " else " .. v
    return name, out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        local name, expr = pick(node)
        local prev = out[#out]
        local dn, dp = decl(prev)
        if name and dn == name then
            prev.text = dp .. " = " .. expr
        elseif name then
            out[#out + 1] = { kind = "raw", text = name .. " = " .. expr }
        else
            out[#out + 1] = node
        end
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.bytecode.instructions"] = [===[
local ins = {}

local conditional = {
    JUMPIF = true,
    JUMPIFNOT = true,
    JUMPIFEQ = true,
    JUMPIFNOTEQ = true,
    JUMPIFLT = true,
    JUMPIFLE = true,
    JUMPIFNOTLT = true,
    JUMPIFNOTLE = true,
    JUMPXEQKNIL = true,
    JUMPXEQKB = true,
    JUMPXEQKN = true,
    JUMPXEQKS = true,
    CMPPROTO = true,
    FORNLOOP = true,
    FORGLOOP = true,
}

local jumps = {
    JUMP = true,
    JUMPBACK = true,
    JUMPX = true,
    FORGPREP = true,
    FORGPREP_INEXT = true,
    FORGPREP_NEXT = true,
}

function ins.name(op)
    return op and op.OpCodeInfo and op.OpCodeInfo.Name or "?"
end

function ins.auxSlots(proto)
    local slots = {}

    for pc = 1, #proto.Instructions do
        if not slots[pc] then
            local op = proto.Instructions[pc]
            if op and op.OpCodeInfo and op.OpCodeInfo.HasAux then
                slots[pc + 1] = true
            end
        end
    end

    return slots
end

function ins.next(proto, pc, auxSlots)
    auxSlots = auxSlots or ins.auxSlots(proto)
    local op = proto.Instructions[pc]

    if not op then
        return pc + 1
    end

    return pc + ((op.OpCodeInfo and op.OpCodeInfo.HasAux) and 2 or 1)
end

function ins.jumpTarget(pc, op)
    if ins.name(op) == "JUMPX" then
        return pc + (op.E or 0) + 1
    end

    return pc + (op.D or 0) + 1
end

function ins.isConditional(op)
    return conditional[ins.name(op)] == true
end

function ins.isUnconditional(op)
    return jumps[ins.name(op)] == true
end

function ins.previousRealPC(auxSlots, pc)
    pc = pc - 1
    while pc >= 1 do
        if not auxSlots[pc] then
            return pc
        end
        pc = pc - 1
    end
end

return ins
]===],
    ["main.config"] = [===[
local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = true,
    types = true,
    selects = true,
    returns = true,
    compound = true,
    inlineast = true,
    callbacks = true,
    booleans = true,
    iridium = nil,
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[k] = v end end
    return out
end
]===],
    ["main.decompiler.context"] = [===[
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")
local tab = require("main.recover.tables")
local ty = require("main.naming.types")

local ctx = {}
ctx.__index = ctx

function ctx.new(proto, ir, naming, up, ast, opt)
    local self = setmetatable({
        proto = proto,
        ir = ir,
        cfg = ir.cfg,
        ssa = ir.ssa,
        naming = naming,
        up = up or {},
        ast = ast,
        opt = opt or {},
        indent = 0,
        declared = {},
        namecall = {},
        consumed = {},
        alias = {},
        str = {},
        vals = {},
        expr = {},
        emit = {},
        group = {},
        tbl = {},
        top = nil,
        bad = {},
        vnames = {},
        nexttmp = 0,
    }, ctx)

    for _, name in ipairs(self.up) do naming:reserve(name) end
    for r = 0, (proto.ParameterCount or 0) - 1 do
        local v = ir.ssa.params[r]
        local name = self:vname(v, r, nil, 1)
        self.declared[name] = 0
    end
    return self
end

function ctx:out(s)
    return self.ast:emit(s)
end

function ctx:trim(depth)
    for name, d in pairs(self.declared) do
        if d >= depth then self.declared[name] = nil end
    end
end

function ctx:ann(r, pc)
    if self.opt.types == false then return nil end
    return ty.text(self.naming:typeAt(r, pc))
end

function ctx:paramann(r)
    if self.opt.types == false then return nil end
    return ty.text(ty.param(self.proto, r))
end

function ctx:badpc(pc, msg)
    local text = "pc " .. tostring(pc) .. ": " .. msg
    self.bad[#self.bad + 1] = text
    self:out("--[[ lumen: " .. text:gsub("%]%]", "] ]") .. " ]]")
end

function ctx:quiet(a, b)
    local pc = self:next(a)
    while pc < b do
        local n = self.ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = self:next(pc)
    end
    return true
end

function ctx:vname(v, r, hint, pc)
    local raw = self.ir:resolve(v)
    v = self.ir:nameid(raw)
    if not v then return self.naming:nameAt(r, pc or 1, hint) end
    local old = self.vnames[v]
    if old then return old end

    local di = pc and self.naming:debugAt(r, pc) or nil
    local ti = pc and self.naming:typeAt(r, pc) or nil
    local src = raw and self.ir.vals[raw] or nil
    local best = self.ir.bestname and self.ir.bestname[v] or nil
    local score = self.ir.namescore and self.ir.namescore[v] or 0
    local name

    if di then
        name = self.naming:nameAt(r, pc, nil)
    elseif best and score >= 80 then
        name = self.naming:unique(best)
    elseif ti then
        name = self.naming:nameAt(r, pc, hint or best)
    elseif best and score >= 55 then
        name = self.naming:unique(best)
    elseif src and src.kind == "param" then
        name = self.naming:unique(hint or (score >= 55 and best or nil) or ("arg" .. tostring(src.reg + 1)))
    elseif hint then
        name = self.naming:unique(hint)
    elseif best then
        name = self.naming:unique(best)
    else
        repeat
            name = "v" .. tostring(self.nexttmp)
            self.nexttmp += 1
        until not self.naming.used[name]
        name = self.naming:unique(name)
    end

    self.vnames[v] = name
    return name
end

function ctx:useName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:veruse(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:defName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:verdef(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:reg(r, hint, pc)
    if self.alias[r] then return self.alias[r] end
    if pc then
        local u = self:veruse(pc, r)
        if u then return self:vname(u, r, hint, pc) end
        local d = self:verdef(pc, r)
        if d then return self:vname(d, r, hint, pc) end
    end
    return self.naming:name(r, hint)
end

function ctx:atom(r, hint, pc)
    return ex.atom(self:useName(pc, r, hint), false)
end

function ctx:veruse(pc, r)
    return self.ir:use(pc, r)
end

function ctx:verdef(pc, r)
    return self.ir:def(pc, r)
end

function ctx:tblmut(use, r)
    return tab.mut(self, use, r)
end

function ctx:usetbl(v, r, pc)
    return tab.use(self, v, r, pc)
end

function ctx:usex(pc, r, hint)
    local v = self:veruse(pc, r)
    if v and self.tbl[v] then
        local node = self:usetbl(v, r, pc)
        if node then return node end
    end
    if v and self.ir.const[v] then return ex.atom(self.ir.const[v], true) end
    if v and self.vals[v] then return self.vals[v] end
    return self:atom(r, hint, pc)
end

function ctx:use(pc, r, hint)
    return ex.str(self:usex(pc, r, hint))
end

function ctx:inline(pc, r, node)
    if self.naming:isDebugAt(r, pc) then return false end
    local v = self:verdef(pc, r)
    if not v or not self.ir.inline[v] then return false end
    if self.ir.const[v] then return true end
    local u = self.ir:only(v)
    if not u or not u.pc then return false end
    if node.stable then return true end
    local defop = self.ir.bypc[pc]
    local useop = self.ir.bypc[u.pc]
    if defop and useop and (defop.name == "GETGLOBAL" or defop.name == "GETIMPORT")
        and (useop.name == "CALL" or useop.name == "CALLFB") and useop.op.A == r then
        return true
    end
    if u.pc == self:next(pc) then return true end
    return self:quiet(pc, u.pc)
end

function ctx:set(pc, r, node, hint, raw)
    local v = self:verdef(pc, r)
    if v then self.expr[v] = node end
    if v and self.ir.dead[v] then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end
    if v and self:inline(pc, r, node) then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end

    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    local fresh = depth == nil or depth > self.indent
    local stmt
    if fresh then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        stmt = self:out("local " .. name .. (an and (": " .. an) or "") .. " = " .. ex.str(node))
    else
        stmt = self:out(name .. " = " .. ex.str(node))
    end
    if v then
        self.emit[v] = { node = stmt, name = name, fresh = fresh, depth = self.indent }
        if raw ~= nil then self.str[v] = raw end
    end
    return name
end

function ctx:decl(r, hint, pc)
    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    if depth == nil or depth > self.indent then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        self:out("local " .. name .. (an and (": " .. an) or ""))
    end
    return name
end

function ctx:multi(pc, regs, rhs, hints, node)
    local list = {}
    local fresh = 0
    local new = {}
    local nodes = {}
    for i, r in ipairs(regs) do
        local name = self:defName(pc, r, hints and hints[i] or nil)
        list[i] = name
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            fresh += 1
            new[#new + 1] = name
        end
    end
    if fresh == #list then
        local typed = {}
        for i, name in ipairs(list) do
            self.declared[name] = self.indent
            local an = self:ann(regs[i], pc)
            typed[i] = name .. (an and (": " .. an) or "")
        end
        nodes[#nodes + 1] = self:out("local " .. table.concat(typed, ", ") .. " = " .. rhs)
    else
        if fresh > 0 then
            for _, name in ipairs(list) do
                local depth = self.declared[name]
                if depth == nil or depth > self.indent then
                    self.declared[name] = self.indent
                    nodes[#nodes + 1] = self:out("local " .. name)
                end
            end
        end
        nodes[#nodes + 1] = self:out(table.concat(list, ", ") .. " = " .. rhs)
    end
    if node then
        local g = { nodes = nodes, new = new, depth = self.indent, node = node }
        for _, r in ipairs(regs) do
            local v = self:verdef(pc, r)
            if v then self.group[v] = g end
        end
    end
    return list
end

function ctx:only(v, a, b, r)
    if not v then return false end
    local block = self.cfg.blockmap[b]
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then
            if u.pc ~= a and u.pc ~= b then return false end
        elseif u.phi then
            local pv = self.ir.vals[self.ir:resolve(u.phi)]
            if not pv or pv.block ~= block or pv.reg ~= r then return false end
        else
            return false
        end
    end
    return true
end

function ctx:hide(v)
    local e = v and self.emit[v]
    if not e or not e.fresh or not e.node then return false end
    e.node.dead = true
    if self.declared[e.name] == e.depth then self.declared[e.name] = nil end
    self.naming:release(e.name)
    return true
end

function ctx:loopx(pc, loop, r)
    local v = self:veruse(pc, r)
    local node = v and self.expr[v]
    if not node or not node.stable or not self:only(v, pc, loop, r) then
        return self:usex(pc, r)
    end
    if self:hide(v) then return node end
    return self:usex(pc, r)
end

function ctx:hidegroup(g, pc, loop, regs)
    if not g or not g.nodes then return false end
    for _, r in ipairs(regs) do
        local v = self:veruse(pc, r)
        if not v or self.group[v] ~= g or not self:only(v, pc, loop, r) then return false end
    end
    for _, node in ipairs(g.nodes) do if node then node.dead = true end end
    for _, name in ipairs(g.new) do
        if self.declared[name] == g.depth then self.declared[name] = nil end
        self.naming:release(name)
    end
    return true
end

function ctx:raw(pc, r)
    local v = self:veruse(pc, r)
    return v and self.str[v] or nil
end

function ctx:next(pc)
    return ins.next(self.proto, pc, self.cfg.aux)
end

function ctx:join(pc)
    local bid = self.cfg.blockmap[pc]
    local id = bid and self.cfg.ipdom[bid]
    local b = id and self.cfg.blocks[id]
    return b and b.startPC or nil
end

function ctx:phlive(v, seen)
    v = self.ir:resolve(v)
    seen = seen or {}
    if not v or seen[v] then return false end
    seen[v] = true
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then return true end
        if u.phi and self:phlive(u.phi, seen) then return true end
    end
    return false
end

function ctx:hoist(pc)
    local bid = self.cfg.blockmap[pc]
    local phis = bid and self.ir.phis[bid]
    if not phis then return end
    local list = {}
    for r, p in pairs(phis) do
        local id = self.ir:resolve(p.id)
        if id == p.id and not self.ir.dead[id] and self:phlive(id) then list[#list + 1] = { r = r, p = p } end
    end
    table.sort(list, function(a, b) return a.r < b.r end)
    for _, item in ipairs(list) do
        local name = self:vname(item.p.id, item.r, nil, pc)
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            self.declared[name] = self.indent
            self:out("local " .. name)
        end
    end
end

return ctx
]===],
    ["main.decompiler.engine"] = [===[
local irbuild = require("main.ir.build")
local irpass = require("main.passes.pipeline")
local names = require("main.naming.resolver")
local lower = require("main.ast.lower")
local astpass = require("main.ast.pipeline")
local printer = require("main.ast.printer")
local context = require("main.decompiler.context")
local ops = require("main.decompiler.ops")
local cond = require("main.recover.conditions")
local branch = require("main.recover.branches")
local loops = require("main.recover.loops")
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")

local decomp = {}
decomp.__index = decomp

local function loopused(st, r, a, b)
    local pc = a
    while pc < b do
        local uses = st.ssa.usesByPC[pc]
        if uses and uses[r] then return true end
        pc = st:next(pc)
    end
    return false
end

function decomp.new(opt)
    return setmetatable({ opt = opt or {} }, decomp)
end

function decomp:_state(proto, up, ph)
    local ir = irbuild.run(proto)
    ir.paramhints = ph or {}
    ir = irpass.run(ir, self.opt)
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    return context.new(proto, ir, naming, up, lower.new(), self.opt)
end

function decomp:_child(proto, up, ph)
    local st = self:_state(proto, up, ph)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    self:_region(st, 1, #proto.Instructions + 1, {})
    local root = astpass.run(st.ast:done(), self.opt)
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local a = op.A
    local old = st.alias[a + 3]
    local lv = st:verdef(loop, a + 3)
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, a + 3, st:next(pc), loop) and "_" or st:vname(lv, a + 3, fall, loop)
    local limit = ex.str(st:loopx(pc, loop, a))
    local step = ex.str(st:loopx(pc, loop, a + 1))
    local init = ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head = head .. ", " .. step end
    st:out(head .. " do")
    st.indent += 1
    st.alias[a + 3] = var
    st.declared[var] = st.indent
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    st.alias[a + 3] = old
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local lop = info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth = (active.loopdepth or 0) + 1
    local vars, old = {}, {}
    for i = 1, n do
        local r = op.A + 2 + i
        old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end

    local src
    local regs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A)
    local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, regs) then
        src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then
        src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then
        src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else
        src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2))
    end

    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do")
    st.indent += 1
    for i = 1, n do
        local r = op.A + 2 + i
        st.alias[r] = vars[i]
        st.declared[vars[i]] = st.indent
    end
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then")
    st.indent += 1
    local old = active.join
    active.join = info.join
    self:_region(st, info.a, info.b, active)
    active.join = old
    st:trim(st.indent)
    st.indent -= 1

    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then
            self:_emitif(st, sub, active, "elseif")
            return
        end
        st:out("else")
        st.indent += 1
        old = active.join
        active.join = info.join
        self:_region(st, info.c, info.d, active)
        active.join = old
        st:trim(st.indent)
        st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start
    active = active or {}

    while pc < stop and pc <= #st.proto.Instructions do
        if st.cfg.aux[pc] or st.consumed[pc] then
            pc += 1
        else
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then
                active["repeat:" .. tostring(pc)] = true
                st:out("repeat")
                st.indent += 1
                local prev = active.loop
                active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active)
                active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch])
                st:trim(st.indent)
                st.indent -= 1
                st:out("until " .. ex.str(x))
                active["repeat:" .. tostring(pc)] = nil
                pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then
                    st:out("while true do")
                    st.indent += 1
                    local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active)
                    active.loop = prev
                    st:trim(st.indent)
                    st.indent -= 1
                    st:out("end")
                    pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]
                    local name = ins.name(op)

                    if name == "FORNPREP" then
                        pc = self:_numfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
                        pc = self:_genfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "CMPPROTO" then
                        local target = ins.jumpTarget(pc, op)
                        local join = st:join(pc)
                        if join and target > pc and target < join and join <= stop then
                            self:_region(st, target, join, active)
                            pc = join
                        else
                            st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop = active.loop
                        local target = ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end")
                            pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then
                                pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc)
                                    st:out("while " .. ex.str(wh.cond) .. " do")
                                    st.indent += 1
                                    local prev = active.loop
                                    active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active)
                                    active.loop = prev
                                    st:trim(st.indent)
                                    st.indent -= 1
                                    st:out("end")
                                    pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then
                                        st:hoist(info.join)
                                        self:_emitif(st, info, active)
                                        pc = info.join
                                    else
                                        st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target))
                                        pc = st:next(pc)
                                    end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target = ins.jumpTarget(pc, op)
                        local loop = active.loop
                        if loop and target == loop.breakpc then
                            st:out("break")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("continue")
                            pc = st:next(pc)
                        elseif target == stop or target == active.join then
                            pc = stop
                        else
                            st:badpc(pc, "unstructured jump -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    else
                        pc = ops.run(self, st, pc)
                    end
                end
            end
        end
    end
    return pc
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    return printer.run(root), {
        cfg = st.cfg,
        ir = st.ir,
        ssa = st.ssa,
        ssaSummary = st.ssa:summary(),
        issues = st.bad,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenDecomp: parsed bytecode has no entry proto")
    self.parsed = parsed
    local src, info = self:decompileProto(proto, {})
    self.parsed = nil
    return src, info
end

return decomp
]===],
    ["main.decompiler.ops"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")
local ex = require("main.output.expr")
local func = require("main.recover.functions")
local tab = require("main.recover.tables")

local ops = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kexpr(proto, i)
    return ex.atom(lit.constant(getk(proto, i)), true)
end

local function call(st, pc, op)
    local a, b, c = op.A, op.B, op.C
    local pending = st.namecall[a]
    local first = pending and a + 2 or a + 1
    local args = {}

    if b == 0 then
        if st.top and st.top.reg >= first then
            for r = first, st.top.reg - 1 do args[#args + 1] = st:use(pc, r) end
            args[#args + 1] = ex.str(st.top.node)
        end
    else
        for r = first, a + b - 1 do args[#args + 1] = st:use(pc, r) end
    end

    local node, hint
    if pending then
        local raw = st:raw(pc, a + 2)
        node = ex.call(ex.atom(pending.obj, false), args, pending.method)
        hint = st.naming.fromMethod(pending.method, raw)
        st.namecall[a] = nil
    else
        local callee = st:usex(pc, a)
        local raw = st:raw(pc, a + 1)
        node = ex.call(callee, args)
        hint = st.naming.fromCall(ex.str(callee), raw)
    end

    st.top = nil
    local rets = c == 0 and -1 or c - 1
    if rets == 0 then
        st:out(ex.str(node))
    elseif rets == -1 then
        st.top = { reg = a, node = node }
        local v = st:verdef(pc, a)
        if v then st.vals[v] = node end
    elseif rets == 1 then
        local v = st:verdef(pc, a)
        if v and st.ir:count(v) == 0 then st:out(ex.str(node)) else st:set(pc, a, node, hint) end
    else
        local regs, hints = {}, {}
        for r = a, a + rets - 1 do
            regs[#regs + 1] = r
            hints[#hints + 1] = r == a and hint or nil
        end
        st:multi(pc, regs, ex.str(node), hints, node)
    end
end

function ops.run(d, st, pc)
    if st.consumed[pc] or st.cfg.aux[pc] then return st:next(pc) end
    local op = st.proto.Instructions[pc]
    local name = ins.name(op)
    local a, b, c, dd = op.A, op.B, op.C, op.D
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" then
    elseif name == "LOADNIL" then st:set(pc, a, ex.atom("nil", true))
    elseif name == "LOADB" then
        st:set(pc, a, ex.atom(b == 1 and "true" or "false", true))
        if c ~= 0 then return pc + c + 1 end
    elseif name == "LOADN" then st:set(pc, a, ex.atom(tostring(dd), true))
    elseif name == "LOADK" then
        local k = getk(st.proto, dd)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "LOADKX" then
        local k = getk(st.proto, aux)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "MOVE" then
        st:set(pc, a, st:usex(pc, b), nil, st:raw(pc, b))
    elseif name == "GETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:set(pc, a, ex.atom(g, false), g)
    elseif name == "SETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:out(g .. " = " .. st:use(pc, a))
    elseif name == "GETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:set(pc, a, ex.atom(u, false), u)
    elseif name == "SETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:out(u .. " = " .. st:use(pc, a))
    elseif name == "GETIMPORT" then
        local v = lit.rawStringConstant(getk(st.proto, dd)) or lit.constant(getk(st.proto, dd))
        st:set(pc, a, ex.atom(v, true), st.naming.fromImport(v))
    elseif name == "GETTABLE" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. st:use(pc, c) .. "]"))
    elseif name == "SETTABLE" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        local kv = st:veruse(pc, c)
        if t and not t.done and sv ~= tv and kv ~= tv then
            t.entries[#t.entries + 1] = { kind = "key", key = st:use(pc, c), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. st:use(pc, c) .. "] = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
        local ki = name == "GETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local suf = lit.identifier(f) and ("." .. f) or ("[" .. lit.string(f) .. "]")
        st:set(pc, a, ex.prop(st:usex(pc, b), suf), st.naming.fromField(f))
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
        local ki = name == "SETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and lit.identifier(f) and sv ~= tv then
            tab.put(t, "field", f, st:usex(pc, a))
        else
            st:out(lit.property(st:use(pc, b), f) .. " = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEN" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. tostring(c + 1) .. "]"))
    elseif name == "SETTABLEN" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and sv ~= tv then
            local idx = c + 1
            local kind = idx == #t.entries + 1 and "list" or "key"
            t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. tostring(c + 1) .. "] = " .. st:use(pc, a))
        end
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        local ki = name == "NAMECALLUDATA" and bit32.band(aux, 0xffff) or aux
        st.namecall[a] = { obj = st:use(pc, b), method = lit.rawStringConstant(getk(st.proto, ki)) or "unknownMethod" }
    elseif name == "CALL" or name == "CALLFB" then
        call(st, pc, op)
    elseif name == "RETURN" then
        if b == 1 then
            st:out("return")
        elseif b == 0 and st.top and st.top.reg >= a then
            local vals = {}
            for r = a, st.top.reg - 1 do vals[#vals + 1] = st:use(pc, r) end
            vals[#vals + 1] = ex.str(st.top.node)
            st:out("return " .. table.concat(vals, ", "))
            st.top = nil
        elseif b == 0 then
            st:badpc(pc, "MULTRET return lost stack top")
            st:out("return " .. st:use(pc, a))
        else
            local vals = {}
            for r = a, a + b - 2 do vals[#vals + 1] = st:use(pc, r) end
            st:out("return " .. table.concat(vals, ", "))
        end
    elseif name == "NEWTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then st.tbl[v] = { reg = a, entries = {}, real = real, done = false }
        else st:set(pc, a, ex.atom("{}", false)) end
    elseif name == "DUPTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then
            local entries, slots = tab.seed(getk(st.proto, dd))
            st.tbl[v] = { reg = a, entries = entries, slots = slots, real = real, done = false }
        else
            st:set(pc, a, ex.atom(lit.constant(getk(st.proto, dd)), false))
        end
    elseif name == "SETLIST" then
        local start = aux
        local tv = st:veruse(pc, a)
        local t = tv and st.tbl[tv]
        local vals = {}
        local mult = false
        if c == 0 then
            if st.top and st.top.reg >= b then
                for r = b, st.top.reg - 1 do vals[#vals + 1] = st:usex(pc, r) end
                vals[#vals + 1] = st.top.node
                mult = true
                st.top = nil
            else
                st:badpc(pc, "SETLIST MULTRET lost stack top")
            end
        else
            for i = 0, c - 2 do vals[#vals + 1] = st:usex(pc, b + i) end
        end
        local selfref = false
        for i = 1, #vals do
            local r = b + i - 1
            if st:veruse(pc, r) == tv then selfref = true break end
        end
        if t and not t.done and not selfref then
            for i, v in ipairs(vals) do
                local idx = start + i - 1
                local kind = idx == #t.entries + 1 and "list" or "key"
                t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = v }
            end
        elseif not mult then
            for i, v in ipairs(vals) do st:out(st:use(pc, a) .. "[" .. tostring(start + i - 1) .. "] = " .. ex.str(v)) end
        else
            local tmp = st.naming:unique("values")
            local args = {}
            for _, v in ipairs(vals) do args[#args + 1] = ex.str(v) end
            st:out("do")
            st.indent += 1
            st:out("local " .. tmp .. " = table.pack(" .. table.concat(args, ", ") .. ")")
            st:out("for i = 1, " .. tmp .. ".n do")
            st.indent += 1
            st:out(st:use(pc, a) .. "[" .. tostring(start) .. " + i - 1] = " .. tmp .. "[i]")
            st.indent -= 1
            st:out("end")
            st.indent -= 1
            st:out("end")
        end
    elseif name == "NEWCLOSURE" then
        local child = st.proto.Protos and st.proto.Protos[dd + 1]
        if child then local caps, nx = func.caps(st, pc, child); func.emit(d, st, pc, a, child, caps, nx)
        else st:badpc(pc, "missing NEWCLOSURE child proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "DUPCLOSURE" then
        local ck = getk(st.proto, dd)
        local child
        if d.parsed and ck and ck.__type == "Closure" then child = d.parsed.Protos[(ck.Value or 0) + 1] end
        if child then func.emit(d, st, pc, a, child, {}, st:next(pc))
        else st:badpc(pc, "missing DUPCLOSURE proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        local map = { ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//", AND = "and", OR = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], st:usex(pc, c)))
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        local map = { ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//", ANDK = "and", ORK = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], kexpr(st.proto, c)))
    elseif name == "SUBRK" or name == "DIVRK" then
        st:set(pc, a, ex.bin(kexpr(st.proto, b), name == "SUBRK" and "-" or "/", st:usex(pc, c)))
    elseif name == "CONCAT" then
        local vals = {}
        for r = b, c do vals[#vals + 1] = st:usex(pc, r) end
        st:set(pc, a, ex.join(vals, ".."))
    elseif name == "NOT" then st:set(pc, a, ex.un("not", st:usex(pc, b)))
    elseif name == "MINUS" then st:set(pc, a, ex.un("-", st:usex(pc, b)))
    elseif name == "LENGTH" then st:set(pc, a, ex.un("#", st:usex(pc, b)))
    elseif name == "GETVARARGS" then
        if b == 0 then
            st.top = { reg = a, node = ex.atom("...", false) }
            local v = st:verdef(pc, a)
            if v then st.vals[v] = st.top.node end
        elseif b == 2 then
            st:set(pc, a, ex.atom("...", false))
        else
            local regs = {}
            for r = a, a + b - 2 do regs[#regs + 1] = r end
            st:multi(pc, regs, "...")
        end
    elseif name == "CAPTURE" or name:match("^FASTCALL") then
    elseif name == "NEWCLASSMEMBER" then
        st:badpc(pc, "experimental NEWCLASSMEMBER approximated")
        local f = lit.rawStringConstant(getk(st.proto, aux)) or "member"
        st:out(lit.property(st:use(pc, a), f) .. " = " .. st:use(pc, c))
    elseif name == "NEWCLASS" then
        st:badpc(pc, "experimental NEWCLASS approximated")
        st:set(pc, a, ex.atom("{}", false))
    else
        st:badpc(pc, "unsupported opcode " .. tostring(name))
    end
    return st:next(pc)
end

return ops
]===],
    ["main.diagnostics.disassembler"] = [===[
local graph = require("main.analysis.graph")
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local dis = {}

local function K(proto, index)
    return proto.Constants and proto.Constants[(index or 0) + 1]
end

local function opname(v)
    return v.OpCodeInfo and v.OpCodeInfo.Name or "?"
end

local function resolve(proto, v)
    local name = opname(v)
    local A, B, C, D = v.A, v.B, v.C, v.D
    local aux = v.AuxValue and v.AuxValue.Value or 0

    if name == "LOADK" then
        return "R" .. A .. " = " .. lit.constant(K(proto, D))
    elseif name == "LOADKX" then
        return "R" .. A .. " = " .. lit.constant(K(proto, aux))
    elseif name == "GETIMPORT" then
        return "R" .. A .. " = " .. lit.constant(K(proto, D))
    elseif name == "GETGLOBAL" then
        return "R" .. A .. " = " .. tostring(lit.rawStringConstant(K(proto, aux)))
    elseif name == "SETGLOBAL" then
        return tostring(lit.rawStringConstant(K(proto, aux))) .. " = R" .. A
    elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
        return "R" .. A .. " = " .. lit.property("R" .. B, lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff))))
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
        return lit.property("R" .. B, lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff)))) .. " = R" .. A
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        return "prepare R" .. A .. " = R" .. B .. ":" .. tostring(lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff))))
    elseif ins.isConditional(v) or ins.isUnconditional(v) or name == "FORNPREP" then
        return "target=" .. tostring(ins.jumpTarget(v.Pc or 0, v))
    end
end

function dis.proto(proto)
    local cfg = graph.build(proto)
    local lines = {}

    for pc = 1, #proto.Instructions do
        if not cfg.aux[pc] then
            local op = proto.Instructions[pc]
            local info = op.OpCodeInfo or {}
            local suffix = resolve(proto, op)

            lines[#lines + 1] = string.format(
                "%04d  %-18s A=%-3s B=%-3s C=%-3s D=%-7s E=%-9s%s",
                pc,
                tostring(info.Name or "?"),
                tostring(op.A),
                tostring(op.B),
                tostring(op.C),
                tostring(op.D),
                tostring(op.E),
                suffix and (" ; " .. suffix) or ""
            )
        end
    end

    return table.concat(lines, "\n")
end

return dis
]===],
    ["main.diagnostics.inspect"] = [===[
local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local irbuild = require("main.ir.build")
local passes = require("main.passes.pipeline")

local view = {}

function view.graph(data)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    return graph.build(proto)
end

function view.ssa(data)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    local cfg = graph.build(proto)
    return ssa.build(proto, cfg)
end

function view.ir(data, opt)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    return passes.run(irbuild.run(proto), opt or {})
end

return view
]===],
    ["main.dump"] = [===[
local env = require("main.runtime.environment")
local st = require("main.runtime.status")
local coref = require("main.runtime.core")

local dump = {}

local function clean(s)
    s = tostring(s or "unnamed")
    s = s:gsub("[%c<>:\"/\\|%?%*]", "_")
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    if s == "" or s == "." or s == ".." then s = "unnamed" end
    return s
end

local function mkdir(path, made)
    if made[path] then return true end
    if type(makefolder) ~= "function" then return false end
    if type(isfolder) == "function" then
        local ok, yes = pcall(isfolder, path)
        if ok and yes then
            made[path] = true
            return true
        end
    end
    local ok = pcall(makefolder, path)
    if ok then made[path] = true end
    return ok
end

local function mkall(path, made)
    local cur = ""
    for part in tostring(path):gmatch("[^/]+") do
        cur = cur == "" and part or cur .. "/" .. part
        mkdir(cur, made)
    end
end

local function rootdir()
    return "LumenDecomp/" .. tostring(game.PlaceId or 0) .. "/dump_" .. tostring(os.time())
end

local function scriptobj(obj)
    local c = obj.ClassName
    return c == "LocalScript" or c == "ModuleScript" or c == "Script"
end

local function parts(obj)
    local rev = {}
    local cur = obj.Parent
    while cur and cur ~= game do
        rev[#rev + 1] = clean(cur.Name)
        cur = cur.Parent
    end
    local out = {}
    for i = #rev, 1, -1 do out[#out + 1] = rev[i] end
    return out
end

local function outpath(root, obj, flat, used, made)
    local seg = parts(obj)
    local dir = root .. "/Scripts"
    if not flat then
        for _, name in ipairs(seg) do dir = dir .. "/" .. name end
    end
    mkall(dir, made)
    local base = clean(obj.Name) .. "." .. clean(obj.ClassName)
    if flat then
        local full = st.path(obj):gsub("%.", "_")
        base = clean(full) .. "." .. clean(obj.ClassName)
    end
    local path = dir .. "/" .. base .. ".luau"
    local n = 2
    while used[path] do
        path = dir .. "/" .. base .. "_" .. tostring(n) .. ".luau"
        n += 1
    end
    used[path] = true
    return path
end

local function scripts(ignorecore)
    local out = {}
    for _, root in ipairs(game:GetChildren()) do
        if not (ignorecore and coref.root(root)) then
            if scriptobj(root) and not (ignorecore and coref.is(root)) then out[#out + 1] = root end
            local ok, list = pcall(root.GetDescendants, root)
            if ok then
                for _, obj in ipairs(list) do
                    if scriptobj(obj) and not (ignorecore and coref.is(obj)) then out[#out + 1] = obj end
                end
            end
        end
    end
    return out
end

local function write(path, data)
    if type(writefile) ~= "function" then return false, "executor does not expose writefile()" end
    local ok, err = pcall(writefile, path, data)
    return ok, err
end

local function fail(stat, obj, err)
    err = tostring(err)
    stat.failed += 1
    local line = st.path(obj) .. " :: " .. err
    stat.errors[#stat.errors + 1] = line
    if stat.failed <= 5 then
        if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] FAIL " .. line .. "\n") end
        warn("[LumenDecomp] FAIL " .. line)
    end
end

local function serial(lumen, list, opt, stat)
    local cache = {}
    local started = os.clock()
    local total = #list
    local decopt = {}
    if type(opt.Options) == "table" then
        for k, v in pairs(opt.Options) do decopt[k] = v end
    end
    stat.found = total
    for i, obj in ipairs(list) do
        local res = lumen:tryDecompile(obj, decopt)
        if res.success and type(res.source) == "string" and res.source ~= "" then
            cache[obj] = res.source
            stat.good += 1
        else
            fail(stat, obj, res.error)
        end
        local elapsed = os.clock() - started
        st.progress("Decompiling", obj, i, total, elapsed > 0 and i / elapsed or nil)
    end
    stat.decompileTime = os.clock() - started
    stat.rate = stat.decompileTime > 0 and total / stat.decompileTime or 0
    return cache
end

local actorcode = [[
local id, src = ...
local ch = get_comm_channel(id)
local ok, api = pcall(function()
    local fn, err = loadstring(src, "@LumenWorker")
    assert(fn, err)
    return fn()
end)
if not ok then
    ch:Fire("boot", false, tostring(api))
    return
end
ch.Event:Connect(function(kind, jid, obj)
    if kind ~= "job" then return end
    local good, out = pcall(function()
        return api:decompile(obj)
    end)
    if good and type(out) == "string" and out ~= "" then
        ch:Fire("done", jid, true, out)
    else
        ch:Fire("done", jid, false, tostring(out))
    end
end)
ch:Fire("boot", true, "")
]]

local function actors(lumen, list, opt, stat)
    if opt.Parallel == false then return nil, "disabled" end
    if #list < 48 then return nil, "too few scripts" end
    if type(run_on_actor) ~= "function" or type(create_comm_channel) ~= "function" or type(get_comm_channel) ~= "function" then
        return nil, "Potassium actor APIs unavailable"
    end
    if type(lumen._workerSource) ~= "function" then return nil, "worker source unavailable" end

    local want = tonumber(opt.MaxWorkers) or 4
    want = math.max(2, math.min(math.floor(want), 32, math.max(2, math.floor(#list / 24))))

    local pool = {}
    local owned = nil
    local ownok = pcall(function()
        local parent = game:GetService("ReplicatedStorage")
        owned = Instance.new("Folder")
        owned.Name = "__LumenWorkers_" .. tostring(math.floor(os.clock() * 1000))
        owned.Archivable = false
        owned.Parent = parent
        for i = 1, want do
            local a = Instance.new("Actor")
            a.Name = "Worker" .. tostring(i)
            a.Archivable = false
            a.Parent = owned
            pool[#pool + 1] = a
        end
    end)

    if not ownok or #pool < 2 then
        if owned then pcall(function() owned:Destroy() end) end
        owned = nil
        pool = {}
        if type(getactors) ~= "function" then return nil, "could not create worker Actors and getactors is unavailable" end
        local ok, existing = pcall(getactors)
        if not ok then return nil, "getactors failed: " .. tostring(existing) end
        if type(existing) ~= "table" or #existing < 2 then return nil, "fewer than 2 usable Actors" end
        pool = existing
        want = math.min(want, #pool)
    else
        task.wait()
    end

    local src = lumen:_workerSource()
    if type(src) ~= "string" or src == "" then
        if owned then pcall(function() owned:Destroy() end) end
        return nil, "empty worker source"
    end

    local ws = {}
    local q = {}
    local booted = 0
    local bootfail = 0

    for i = 1, want do
        local id, ch = create_comm_channel()
        local w = { id = id, ch = ch, actor = pool[i], ready = false, dead = false, busy = false, sent = 0 }
        w.con = ch.Event:Connect(function(kind, a, b, c)
            if kind == "boot" then
                if a then
                    if not w.ready then booted += 1 end
                    w.ready = true
                else
                    if not w.dead then bootfail += 1 end
                    w.dead = true
                    w.err = tostring(b)
                end
            elseif kind == "done" then
                q[#q + 1] = { w = w, jid = a, ok = b, out = c }
            end
        end)
        ws[#ws + 1] = w
        local rok, rerr = pcall(run_on_actor, w.actor, actorcode, id, src)
        if not rok then
            w.dead = true
            w.err = tostring(rerr)
            bootfail += 1
        end
    end

    local bt = os.clock()
    while booted + bootfail < #ws and os.clock() - bt < 8 do task.wait(0.01) end

    local live = {}
    for _, w in ipairs(ws) do
        if w.ready and not w.dead then live[#live + 1] = w end
    end
    if #live < 2 then
        local why = {}
        for _, w in ipairs(ws) do
            if w.err then why[#why + 1] = w.err end
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
        if owned then pcall(function() owned:Destroy() end) end
        return nil, "worker boot failed" .. (#why > 0 and (": " .. table.concat(why, " | ")) or "")
    end

    stat.parallel = #live
    stat.found = #list
    local cache = {}
    local nextjob = 1
    local done = 0
    local active = {}
    local started = os.clock()

    local function send(w)
        if w.dead or nextjob > #list then return end
        local jid = nextjob
        nextjob += 1
        w.busy = true
        w.sent = os.clock()
        w.jid = jid
        active[jid] = true
        w.ch:Fire("job", jid, list[jid])
    end

    for _, w in ipairs(live) do send(w) end

    while done < #list do
        while #q > 0 do
            local r = table.remove(q, 1)
            local w = r.w
            local jid = r.jid
            if active[jid] then
                active[jid] = nil
                done += 1
                w.busy = false
                local obj = list[jid]
                if r.ok and type(r.out) == "string" and r.out ~= "" then
                    cache[obj] = r.out
                    stat.good += 1
                else
                    local res = lumen:tryDecompile(obj, opt.Options)
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                        w.bad = (w.bad or 0) + 1
                        if w.bad >= 2 then w.dead = true end
                    else
                        fail(stat, obj, res.error or r.out)
                    end
                end
                local elapsed = os.clock() - started
                st.progress("Parallel decompile x" .. tostring(#live), obj, done, #list, elapsed > 0 and done / elapsed or nil)
                send(w)
            end
        end

        local now = os.clock()
        for _, w in ipairs(live) do
            if w.busy and now - w.sent > 60 then
                local jid = w.jid
                if active[jid] then
                    active[jid] = nil
                    w.dead = true
                    w.busy = false
                    local obj = list[jid]
                    local res = lumen:tryDecompile(obj, opt.Options)
                    done += 1
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                    else
                        fail(stat, obj, res.error or "parallel worker timeout")
                    end
                    local elapsed = os.clock() - started
                    st.progress("Parallel fallback", obj, done, #list, elapsed > 0 and done / elapsed or nil)
                end
            end
        end

        local alive = 0
        for _, w in ipairs(live) do if not w.dead then alive += 1 end end
        if alive == 0 and done < #list then
            for jid = 1, #list do
                if not cache[list[jid]] and active[jid] == nil and jid < nextjob then
                elseif jid >= nextjob then
                    local obj = list[jid]
                    local res = lumen:tryDecompile(obj, opt.Options)
                    done += 1
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                    else
                        fail(stat, obj, res.error)
                    end
                end
            end
            break
        end

        task.wait(0.005)
    end

    for _, w in ipairs(ws) do if w.con then pcall(function() w.con:Disconnect() end) end end
    if owned then pcall(function() owned:Destroy() end) end
    stat.decompileTime = os.clock() - started
    stat.rate = stat.decompileTime > 0 and #list / stat.decompileTime or 0
    return cache
end

local function writetree(root, list, cache, treeon, stat, made)
    local used = {}
    local total = #list
    local started = os.clock()
    local written = 0
    for i, obj in ipairs(list) do
        local src = cache[obj]
        if type(src) == "string" then
            local path = outpath(root, obj, not treeon, used, made)
            local ok, err = write(path, src)
            if ok then
                written += 1
            else
                stat.writeFailed += 1
                stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. tostring(err)
            end
        end
        st.progress("Writing source tree", obj, i, total)
    end
    stat.written = written
    stat.writeTime = os.clock() - started
end

local function summary(root, stat)
    local lines = {
        "LumenDecomp dump",
        "PlaceId: " .. tostring(game.PlaceId),
        "Scripts found: " .. tostring(stat.found),
        "Decompiled: " .. tostring(stat.good),
        "Failed/skipped: " .. tostring(stat.failed),
        "Source files written: " .. tostring(stat.written or 0),
        "Write failures: " .. tostring(stat.writeFailed),
        "Binary: " .. tostring(stat.binary),
        "Workers: " .. tostring(stat.parallel or 1),
        "Decompile seconds: " .. string.format("%.3f", stat.decompileTime or 0),
        "Decompile rate: " .. string.format("%.2f scripts/s", stat.rate or 0),
        "Write seconds: " .. string.format("%.3f", stat.writeTime or 0),
        "",
    }
    if #stat.errors > 0 then
        lines[#lines + 1] = "Errors:"
        for _, e in ipairs(stat.errors) do lines[#lines + 1] = e end
    end
    write(root .. "/summary.txt", table.concat(lines, "\n"))
end

function dump.run(lumen, opt)
    opt = opt or {}
    local root = opt.Root or rootdir()
    local stat = { found = 0, good = 0, failed = 0, written = 0, writeFailed = 0, binary = false, errors = {}, decompileTime = 0, writeTime = 0, rate = 0, parallel = 1 }
    local made = {}
    mkall(root, made)
    st.set("Starting", tostring(game.Name) .. " | " .. root)

    local list
    local cache
    if opt.Decompile and (opt.Tree or not opt.Binary) then
        list = scripts(opt.IgnoreCoreScripts == true)
        local pok, pout, preason = pcall(actors, lumen, list, opt, stat)
        if pok then
            cache = pout
            if not cache and preason and opt.Parallel ~= false then
                if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel unavailable: " .. tostring(preason) .. "\n") end
                warn("[LumenDecomp] parallel unavailable: " .. tostring(preason))
            end
        else
            if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel fallback: " .. tostring(pout) .. "\n") end
            warn("[LumenDecomp] parallel fallback: " .. tostring(pout))
        end
        if not cache then cache = serial(lumen, list, opt, stat) end
        writetree(root, list, cache, opt.Tree, stat, made)
    end

    if opt.Binary then
        st.set("Saving binary", cache and "reusing decompiled source cache" or tostring(game.Name))
        local file = root .. "/FullGame.rbxl"
        local ok, err = pcall(function()
            lumen:save(game, file, {
                Binary = true,
                Decompile = opt.Decompile == true,
                SourceCache = cache,
                IgnoreCoreScripts = opt.IgnoreCoreScripts == true,
                NilInstances = opt.NilInstances == true,
                RemovePlayerCharacters = opt.RemovePlayerCharacters == true,
                SavePlayers = opt.SavePlayers == true,
                MaxThreads = opt.MaxThreads or 8,
                DecompileIgnore = opt.IgnoreCoreScripts and { "Chat", "CoreGui", "CorePackages", "RobloxReplicatedStorage", "CoreScriptSyncService" } or opt.DecompileIgnore,
                ShowStatus = false,
            })
        end)
        stat.binary = ok
        if not ok then stat.errors[#stat.errors + 1] = "binary :: " .. tostring(err) end
    end

    summary(root, stat)
    if stat.good == 0 and stat.failed > 0 then
        st.done("FAILED - 0 decompiled, " .. tostring(stat.failed) .. " failed | " .. tostring(stat.errors[1] or "unknown failure"))
    else
        local mode = stat.parallel and stat.parallel > 1 and (" x" .. tostring(stat.parallel)) or ""
        st.done("Done - " .. tostring(stat.good) .. " decompiled, " .. tostring(stat.failed) .. " failed | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
    end
    return root, stat
end

function dump.auto(lumen, boot)
    local e = env.get()

    local function val(name)
        if type(boot) == "table" and boot[name] ~= nil then return boot[name] end
        local v = rawget(e, name)
        if v ~= nil then return v end
        if type(getfenv) == "function" then
            for level = 0, 8 do
                local ok, scope = pcall(getfenv, level)
                if ok and type(scope) == "table" then
                    v = rawget(scope, name)
                    if v ~= nil then return v end
                end
            end
        end
        return rawget(_G, name)
    end

    local binary = val("Binary") == true
    local decomp = val("Decompile") == true
    local treeon = val("Tree") == true
    local ignorecore = val("IgnoreCoreScripts") == true
    local parallel = val("Parallel")
    if parallel == nil then parallel = true else parallel = parallel == true end
    local maxworkers = tonumber(val("MaxWorkers")) or 4
    local flags = "Binary=" .. tostring(binary) .. " | Decompile=" .. tostring(decomp) .. " | Tree=" .. tostring(treeon) .. " | IgnoreCoreScripts=" .. tostring(ignorecore) .. " | Parallel=" .. tostring(parallel) .. " | MaxWorkers=" .. tostring(maxworkers)

    st.set("Loaded", "v" .. tostring(lumen.Version) .. " | " .. flags)
    print("[LumenDecomp] " .. flags)
    if not binary and not decomp and not treeon then
        task.delay(2, function() st.done("Loaded - idle | " .. flags) end)
        return false
    end
    if rawget(e, "__LumenDump") then
        st.set("Already running")
        return false
    end

    e.__LumenDump = true
    st.set("Starting dump", flags)
    task.spawn(function()
        local ok, err = pcall(function()
            dump.run(lumen, { Binary = binary, Decompile = decomp, Tree = treeon, IgnoreCoreScripts = ignorecore, Parallel = parallel, MaxWorkers = maxworkers })
        end)
        e.__LumenDump = nil
        if not ok then
            st.set("ERROR", tostring(err))
            warn("[LumenDecomp] " .. tostring(err))
        end
    end)
    return true
end

return dump
]===],
    ["main.ir.block"] = [===[
local block = {}
block.__index = block

function block.new(src)
    return setmetatable({
        id = src.id,
        first = src.startPC,
        last = src.endPC,
        pcs = src.pcs,
        preds = src.predecessors,
        succs = src.successors,
        ops = {},
    }, block)
end

return block
]===],
    ["main.ir.build"] = [===[
local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local regs = require("main.analysis.registers")
local ins = require("main.bytecode.instructions")
local fx = require("main.ir.effects")
local fn = require("main.ir.function")
local val = require("main.ir.value")
local block = require("main.ir.block")

local build = {}

function build.run(proto)
    local cfg = graph.build(proto)
    local flow = ssa.build(proto, cfg)
    local out = fn.new(proto, cfg, flow)

    for id, src in ipairs(flow.versions) do
        out.vals[id] = val.new(id, src)
        if src.dead then out.dead[id] = true end
    end

    for bid, phis in pairs(flow.phisByBlock) do
        local dst = {}
        out.phis[bid] = dst
        for reg, p in pairs(phis) do
            dst[reg] = { id = p.id, reg = reg, inputs = p.inputs, missing = p.missing }
        end
    end

    for _, src in ipairs(cfg.blocks) do
        local b = block.new(src)
        out.blocks[b.id] = b
        for _, pc in ipairs(src.pcs) do
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local reads, writes = regs.readWrite(op)
            local n = {
                pc = pc,
                op = op,
                name = name,
                block = b.id,
                reads = reads,
                writes = writes,
                pure = fx.pure(name),
                drop = fx.drop(name),
                quiet = fx.quiet(name),
                effect = fx.effect(name),
                term = fx.term(name),
            }
            out.ops[#out.ops + 1] = n
            out.bypc[pc] = n
            b.ops[#b.ops + 1] = n
        end
    end

    out:reindex()
    return out
end

return build
]===],
    ["main.ir.effects"] = [===[
local fx = {}

local pure = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, GETIMPORT = true, GETGLOBAL = true,
    GETTABLE = true, GETTABLEKS = true, GETTABLEN = true, GETUDATAKS = true,
    ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true,
    IDIV = true, ADDK = true, SUBK = true, MULK = true, DIVK = true,
    MODK = true, POWK = true, IDIVK = true, SUBRK = true, DIVRK = true,
    AND = true, OR = true, ANDK = true, ORK = true, CONCAT = true,
    NOT = true, MINUS = true, LENGTH = true, NEWTABLE = true, DUPTABLE = true,
    GETVARARGS = true,
}

local drop = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, AND = true, OR = true, ANDK = true, ORK = true,
    NOT = true, NEWTABLE = true, DUPTABLE = true, GETVARARGS = true,
}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true,
    LOADKX = true, MOVE = true, GETUPVAL = true, PREPVARARGS = true,
    COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

function fx.pure(name)
    return pure[name] == true
end

function fx.drop(name)
    return drop[name] == true
end

function fx.quiet(name)
    return quiet[name] == true
end

function fx.term(name)
    return term[name] == true
end

function fx.effect(name)
    if drop[name] or quiet[name] or term[name] then return false end
    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name == "CAPTURE" then return false end
    return true
end

return fx
]===],
    ["main.ir.function"] = [===[
local fn = {}
fn.__index = fn

function fn.new(proto, cfg, flow)
    return setmetatable({
        proto = proto,
        cfg = cfg,
        ssa = flow,
        vals = {},
        blocks = {},
        ops = {},
        bypc = {},
        phis = {},
        alias = {},
        usemap = {},
        inline = {},
        dead = {},
        const = {},
    }, fn)
end

function fn:resolve(id)
    local seen = {}
    while id and self.alias[id] and not seen[id] do
        seen[id] = true
        id = self.alias[id]
    end
    return id
end

function fn:use(pc, reg)
    local uses = self.ssa.usesByPC[pc]
    return self:resolve(uses and uses[reg] or nil)
end

function fn:def(pc, reg)
    local defs = self.ssa.defsByPC[pc]
    return self:resolve(defs and defs[reg] or nil)
end

function fn:uses(id)
    id = self:resolve(id)
    return id and self.usemap[id] or nil
end

function fn:count(id)
    local uses = self:uses(id)
    return uses and #uses or 0
end

function fn:only(id)
    local uses = self:uses(id)
    return uses and #uses == 1 and uses[1] or nil
end

function fn:nameid(id)
    id = self:resolve(id)
    return id and ((self.family and self.family[id]) or id) or nil
end

function fn:reindex()
    local map = {}
    for pc, uses in pairs(self.ssa.usesByPC) do
        for reg, raw in pairs(uses) do
            local id = self:resolve(raw)
            if id then
                local list = map[id] or {}
                map[id] = list
                list[#list + 1] = { pc = pc, reg = reg, block = self.cfg.blockmap[pc] }
            end
        end
    end
    for bid, phis in pairs(self.phis) do
        for reg, p in pairs(phis) do
            if not self.dead[p.id] then
                local clean = {}
                for raw in pairs(p.inputs or {}) do
                    local id = self:resolve(raw)
                    if id and id ~= p.id then clean[id] = true end
                end
                p.inputs = clean
                for id in pairs(clean) do
                    local list = map[id] or {}
                    map[id] = list
                    list[#list + 1] = { phi = p.id, block = bid, reg = reg }
                end
            end
        end
    end
    self.usemap = map
    for id, v in pairs(self.vals) do v.uses = map[id] or {} end
end

return fn
]===],
    ["main.ir.value"] = [===[
local val = {}
val.__index = val

function val.new(id, src)
    return setmetatable({
        id = id,
        reg = src.reg,
        pc = src.pc,
        block = src.block,
        kind = src.kind,
        dead = src.dead == true,
        alias = nil,
        uses = {},
        const = nil,
        inline = false,
    }, val)
end

return val
]===],
    ["main.naming.debug_names"] = [===[
local id = require("main.naming.identifiers")

local dbg = {}

function dbg.ranges(proto)
    local out = {}
    if not (proto and proto.HasDebugInfo and proto.LocalVariables) then return out end

    for _, info in ipairs(proto.LocalVariables) do
        local reg = info.Register
        local name = id.clean(info.Name)
        if name then
            local list = out[reg] or {}
            out[reg] = list
            list[#list + 1] = {
                name = name,
                first = info.StartPc or 0,
                last = info.EndPc or math.huge,
            }
        end
    end

    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.first == b.first then return a.last < b.last end
            return a.first < b.first
        end)
    end

    return out
end

function dbg.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.first and p < info.last then
            if not best or info.first >= best.first then best = info end
        end
    end
    return best
end

return dbg
]===],
    ["main.naming.identifiers"] = [===[
local id = {}

local kw = {
    ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true,
    ["end"] = true, ["false"] = true, ["for"] = true, ["function"] = true, ["if"] = true,
    ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true, ["or"] = true,
    ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
    ["until"] = true, ["while"] = true,
}

function id.valid(value)
    return type(value) == "string"
        and value:match("^[A-Za-z_][A-Za-z0-9_]*$")
        and not kw[value]
end

function id.clean(value)
    if type(value) ~= "string" then return nil end

    value = value:gsub("[^A-Za-z0-9_]", "_")
    value = value:gsub("_+", "_")
    value = value:gsub("^_+", "")
    value = value:gsub("_+$", "")

    if value == "" then return nil end
    if value:match("^[0-9]") then value = "_" .. value end
    if kw[value] then value = value .. "Value" end

    return value
end

function id.lowerCamel(value)
    value = id.clean(value)
    if not value then return nil end

    if value:match("^[A-Z][A-Z0-9_]+$") then
        value = value:lower()
    end

    return value:sub(1, 1):lower() .. value:sub(2)
end

return id
]===],
    ["main.naming.resolver"] = [===[
local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local dbg = require("main.naming.debug_names")
local ty = require("main.naming.types")

local names = {}
names.__index = names

function names.new(stats, opt, proto)
    return setmetatable({
        used = {},
        regs = {},
        locals = {},
        stats = stats or {},
        opt = opt or {},
        proto = proto,
        debug = dbg.ranges(proto),
        typed = ty.ranges(proto),
    }, names)
end

function names:unique(base)
    base = id.clean(base) or "value"
    if not self.used[base] then
        self.used[base] = true
        return base
    end
    local n = 2
    while self.used[base .. n] do n += 1 end
    local name = base .. n
    self.used[name] = true
    return name
end

function names:stable(reg)
    local stat = self.stats[reg]
    if not stat then return true end
    return (stat.writes or 0) <= 1 or self.opt.aggressive == true
end

function names:debugAt(reg, pc)
    return dbg.at(self.debug, reg, pc)
end

function names:typeAt(reg, pc)
    return ty.at(self.typed, reg, pc)
end

function names:isDebugAt(reg, pc)
    return self:debugAt(reg, pc) ~= nil
end

function names:nameAt(reg, pc, hint)
    local info = self:debugAt(reg, pc)
    if info then
        local key = "d:" .. tostring(reg) .. ":" .. tostring(info.first) .. ":" .. tostring(info.last) .. ":" .. info.name
        local old = self.locals[key]
        if old then return old end
        local name = self:unique(info.name)
        self.locals[key] = name
        return name
    end

    local typed = self:typeAt(reg, pc)
    if typed then
        local key = "t:" .. tostring(reg) .. ":" .. tostring(typed.StartPc) .. ":" .. tostring(typed.EndPc)
        local old = self.locals[key]
        if old then return old end
        local base = hint or ty.hint(typed)
        if base then
            local name = self:unique(base)
            self.locals[key] = name
            return name
        end
    end

    if not hint and pc == 1 then
        hint = ty.hint(ty.param(self.proto, reg))
        if not hint and reg < (self.proto.ParameterCount or 0) then hint = "arg" .. tostring(reg + 1) end
    end
    return self:name(reg, hint)
end

function names:name(reg, hint)
    local old = self.regs[reg]
    if old then return old end
    local base
    if hint and self:stable(reg) then base = id.clean(hint) end
    base = base or ("v" .. tostring(reg))
    local name = self:unique(base)
    self.regs[reg] = name
    return name
end

function names:reserve(name)
    name = id.clean(name)
    if name then self.used[name] = true end
    return name
end

function names:release(name)
    if name then self.used[name] = nil end
end

names.fromImport = rbx.fromImport
names.fromField = rbx.fromField
names.fromMethod = rbx.fromMethod
names.fromCall = rbx.fromCall

return names
]===],
    ["main.naming.roblox"] = [===[
local id = require("main.naming.identifiers")
local words = require("main.naming.words")

local rbx = {}

local fields = {
    LocalPlayer = "localPlayer", Character = "character", Humanoid = "humanoid",
    HumanoidRootPart = "rootPart", PrimaryPart = "primaryPart", CurrentCamera = "camera",
    PlayerGui = "playerGui", Backpack = "backpack", PlayerScripts = "playerScripts",
    Mouse = "mouse", Parent = "parent", Position = "position", CFrame = "cframe",
    Size = "size", Name = "name", Value = "value", Enabled = "enabled",
    Visible = "visible", Health = "health", MaxHealth = "maxHealth", Team = "team",
    UserId = "userId", CharacterAdded = "characterAdded", OnClientEvent = "event",
    OnServerEvent = "event", Touched = "touched", AbsolutePosition = "position",
    AbsoluteSize = "size", AssemblyLinearVelocity = "velocity", AssemblyAngularVelocity = "angularVelocity",
}

function rbx.fromImport(path)
    if type(path) ~= "string" then return nil end
    local tail = path:match("([A-Za-z_][A-Za-z0-9_]*)$")
    if not tail then return nil end
    if path:match("^game%.") or path == tail then return id.clean(tail) end
    return id.lowerCamel(tail)
end

function rbx.fromField(field)
    return fields[field] or id.lowerCamel(field)
end

function rbx.fromMethod(method, arg)
    if method == "GetService" and arg then return id.lowerCamel(arg) end
    if method == "WaitForChild" or method == "FindFirstChild" or method == "FindFirstAncestor" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "child"
    end
    if method == "FindFirstChildOfClass" or method == "FindFirstChildWhichIsA" or method == "FindFirstAncestorOfClass" or method == "FindFirstAncestorWhichIsA" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "instance"
    end
    if method == "IsA" then
        if arg then return "is" .. arg:gsub("^%l", string.upper) end
        return "isType"
    end
    if method == "GetPlayerFromCharacter" then return "player" end
    if method == "GetPlayers" then return "playerList" end
    if method == "GetChildren" then return "children" end
    if method == "GetDescendants" then return "descendants" end
    if method == "GetMouse" then return "mouse" end
    if method == "GetPivot" then return "pivot" end
    if method == "GetAttribute" then return arg and id.lowerCamel(arg) or "attribute" end
    if method == "GetAttributes" then return "attributes" end
    if method == "GetPropertyChangedSignal" then return "signal" end
    if method == "Clone" then return "clone" end
    if method == "Connect" or method == "ConnectParallel" then return "connection" end
    if method == "Raycast" then return "raycastResult" end
    if method == "GetPartsInPart" or method == "GetPartBoundsInBox" or method == "GetPartBoundsInRadius" then return "parts" end
    if method == "JSONDecode" then return "data" end
    if method == "JSONEncode" then return "json" end
    if method == "GenerateGUID" then return "guid" end
    if method == "InvokeServer" or method == "Invoke" then return "result" end
    return words.method(method)
end

function rbx.fromCall(callee, arg)
    if callee == "Instance.new" and arg then return id.lowerCamel(arg) end
    local ctor = {
        ["Vector3.new"] = "vector", ["Vector2.new"] = "vector", ["CFrame.new"] = "cframe",
        ["CFrame.lookAt"] = "cframe", ["Color3.new"] = "color", ["Color3.fromRGB"] = "color",
        ["Color3.fromHSV"] = "color", ["UDim.new"] = "udim", ["UDim2.new"] = "udim2",
        ["UDim2.fromScale"] = "udim2", ["UDim2.fromOffset"] = "udim2",
        ["TweenInfo.new"] = "tweenInfo", ["RaycastParams.new"] = "raycastParams",
        ["OverlapParams.new"] = "overlapParams", ["Random.new"] = "random",
        ["NumberRange.new"] = "range", ["NumberSequence.new"] = "sequence",
        ["ColorSequence.new"] = "colorSequence", ["Region3.new"] = "region",
        ["Rect.new"] = "rect",
    }
    if ctor[callee] then return ctor[callee] end
    if callee == "require" then return "module" end
    if callee == "tonumber" then return "num" end
    if callee == "tostring" then return "text" end
    if callee == "typeof" or callee == "type" then return "typeName" end
    if callee == "table.clone" then return "copy" end
    if callee == "table.pack" then return "values" end
    if callee == "string.split" then return "parts" end
    if callee == "task.spawn" or callee == "task.defer" then return "thread" end
    return words.call(callee)
end

return rbx
]===],
    ["main.naming.types"] = [===[
local id = require("main.naming.identifiers")

local types = {}

local map = {
    boolean = "flag",
    number = "num",
    integer = "num",
    string = "text",
    table = "data",
    ["function"] = "fn",
    thread = "thread",
    vector = "vec",
    buffer = "buf",
    userdata = "obj",
}

function types.hint(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    return map[name] or id.lowerCamel(name:gsub("^userdata#", "obj"))
end

function types.text(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    local safe = { boolean = true, number = true, string = true, buffer = true, integer = true, any = true }
    local out
    if info.UserdataName and id.valid(info.UserdataName) then out = info.UserdataName
    elseif safe[name] then out = name end
    if not out then return nil end
    if info.IsOptional and out ~= "any" then out = out .. "?" end
    return out
end

function types.ranges(proto)
    local out = {}
    for _, info in ipairs(proto and proto.LocalTypes or {}) do
        local reg = info.Register
        local list = out[reg] or {}
        out[reg] = list
        list[#list + 1] = info
    end
    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.StartPc == b.StartPc then return a.EndPc < b.EndPc end
            return a.StartPc < b.StartPc
        end)
    end
    return out
end

function types.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.StartPc and p < info.EndPc then
            if not best or info.StartPc >= best.StartPc then best = info end
        end
    end
    return best
end

function types.param(proto, reg)
    local fn = proto and proto.FunctionType
    local list = fn and fn.ParameterTypes
    return list and list[reg + 1] or nil
end

return types
]===],
    ["main.naming.words"] = [===[
local id = require("main.naming.identifiers")

local w = {}

local bad = {
    get = true, find = true, fetch = true, load = true, read = true, make = true,
    create = true, build = true, new = true, resolve = true, compute = true,
    calc = true, clone = true, wait = true, require = true,
}

local keep = {
    is = true, has = true, can = true, should = true, did = true, was = true,
}

local function tail(s)
    if type(s) ~= "string" then return nil end
    return s:match("([%a_][%w_]*)$")
end

function w.clean(s)
    if type(s) ~= "string" then return nil end
    s = s:gsub("^_+", ""):gsub("_+$", "")
    if s == "" then return nil end
    return id.clean(id.lowerCamel(s))
end

function w.singular(s)
    s = w.clean(s)
    if not s then return nil end
    local low = s:lower()
    if low:match("ies$") and #s > 4 then return s:sub(1, -4) .. "y" end
    if low:match("sses$") or low:match("shes$") or low:match("ches$") or low:match("xes$") or low:match("zes$") then
        return s:sub(1, -3)
    end
    if low:sub(-1) == "s" and low:sub(-2) ~= "ss" and #s > 3 then return s:sub(1, -2) end
    return s
end

function w.call(s)
    s = tail(s)
    if not s then return nil end
    local lc = id.lowerCamel(s)
    for pre in pairs(bad) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then
            local c = lc:sub(n + 1, n + 1)
            if c:match("[A-Z]") or s:sub(n + 1, n + 1):match("[A-Z]") then
                return w.clean(s:sub(n + 1))
            end
        end
    end
    for pre in pairs(keep) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then return w.clean(s) end
    end
    return w.clean(s)
end

function w.method(s)
    if type(s) ~= "string" then return nil end
    if s == "Connect" then return "connection" end
    if s == "Clone" then return "clone" end
    if s == "GetChildren" then return "children" end
    if s == "GetDescendants" then return "descendants" end
    if s == "GetAttributes" then return "attributes" end
    if s == "GetAttribute" then return "attribute" end
    if s == "GetPropertyChangedSignal" then return "signal" end
    return w.call(s)
end

function w.field(s)
    return w.clean(s)
end

function w.iter(s)
    local x = w.singular(s)
    if not x or x == s and (s == "data" or s == "list" or s == "array" or s == "items") then return "item" end
    return x or "item"
end

return w
]===],
    ["main.output.expr"] = [===[
local expr = {}

local prec = {
    ["or"] = 1,
    ["and"] = 2,
    ["=="] = 3,
    ["~="] = 3,
    ["<"] = 3,
    ["<="] = 3,
    [">"] = 3,
    [">="] = 3,
    [".."] = 4,
    ["+"] = 5,
    ["-"] = 5,
    ["*"] = 6,
    ["/"] = 6,
    ["//"] = 6,
    ["%"] = 6,
    ["^"] = 8,
}

local function node(s, p, stable, kind, a, b, op)
    return { s = s, p = p or 99, stable = stable == true, kind = kind, a = a, b = b, op = op }
end

local function text(v)
    return type(v) == "table" and v.s or tostring(v)
end

local function wrap(v, p, right, op)
    if type(v) ~= "table" then return tostring(v) end
    if v.p < p then return "(" .. v.s .. ")" end
    if v.p == p then
        if p == 3 then return "(" .. v.s .. ")" end
        if op == "^" and not right then return "(" .. v.s .. ")" end
        if op == ".." and not right then return "(" .. v.s .. ")" end
        if right and op ~= "^" and op ~= ".." then return "(" .. v.s .. ")" end
    end
    return v.s
end

function expr.atom(s, stable)
    return node(s, 99, stable, "atom")
end

function expr.bin(a, op, b)
    local p = prec[op] or 5
    return node(wrap(a, p, false, op) .. " " .. op .. " " .. wrap(b, p, true, op), p, a.stable and b.stable, "bin", a, b, op)
end

function expr.un(op, a)
    local p = 7
    local s = type(a) == "table" and (a.p < p and "(" .. a.s .. ")" or a.s) or tostring(a)
    if op == "not" then
        return node("not " .. s, p, a.stable, "un", a, nil, op)
    end
    return node(op .. s, p, a.stable, "un", a, nil, op)
end

function expr.prop(a, field)
    local base = type(a) == "table" and (a.p < 9 and "(" .. a.s .. ")" or a.s) or tostring(a)
    return node(base .. field, 10, false, "prop", a, field)
end

function expr.call(fn, args, method)
    local base = type(fn) == "table" and (fn.p < 9 and "(" .. fn.s .. ")" or fn.s) or tostring(fn)
    if method then base = base .. ":" .. method end
    return node(base .. "(" .. table.concat(args, ", ") .. ")", 10, false, "call", fn, args, method)
end

function expr.join(list, op)
    local out = list[1]
    for i = 2, #list do out = expr.bin(out, op, list[i]) end
    return out
end

function expr.str(v)
    return text(v)
end

return expr
]===],
    ["main.output.literals"] = [===[
local id = require("main.naming.identifiers")

local lit = {}

function lit.identifier(value)
    return id.valid(value)
end

function lit.number(value)
    if value ~= value then return "(0 / 0)" end
    if value == math.huge then return "math.huge" end
    if value == -math.huge then return "-math.huge" end
    if value == 0 and 1 / value == -math.huge then return "-0.0" end
    return tostring(value)
end

function lit.string(value)
    return string.format("%q", value)
end

function lit.rawStringConstant(constant)
    if not constant then return nil end

    if constant.__type == "String" then
        local ok, result = pcall(buffer.tostring, constant.Value)
        if ok then return result end
    elseif constant.__type == "Import" then
        local parts = {}
        for _, item in ipairs(constant.Value) do
            local ok, result = pcall(buffer.tostring, item.Value)
            parts[#parts + 1] = ok and result or "?"
        end
        return table.concat(parts, ".")
    end

    return nil
end

local function tableKey(key)
    local raw = lit.rawStringConstant(key)
    if raw then
        if lit.identifier(raw) then
            return raw
        end
        return "[" .. lit.string(raw) .. "]"
    end

    return "[" .. lit.constant(key) .. "]"
end

function lit.constant(constant)
    if not constant then return "nil" end

    local kind = constant.__type

    if kind == "Nil" then
        return "nil"
    elseif kind == "Boolean" then
        return tostring(constant.Value)
    elseif kind == "Number" then
        return lit.number(constant.Value)
    elseif kind == "Integer" then
        local value = constant.Value
        if constant.IsNegative and type(value) == "number" and value > 0 then
            value = -value
        end
        return type(value) == "number" and lit.number(value) or tostring(value)
    elseif kind == "String" then
        return lit.string(lit.rawStringConstant(constant) or "")
    elseif kind == "Import" then
        return lit.rawStringConstant(constant) or "nil"
    elseif kind == "Vector" then
        return "Vector3.new(" .. lit.number(constant.X) .. ", " .. lit.number(constant.Y) .. ", " .. lit.number(constant.Z) .. ")"
    elseif kind == "Table" then
        return "{}"
    elseif kind == "TableWithConstants" then
        local parts = {}
        for _, pair in ipairs(constant.Value or {}) do
            local key = tableKey(pair.Key)
            local value = pair.Value and lit.constant(pair.Value) or "nil"
            parts[#parts + 1] = key .. " = " .. value
        end
        return "{ " .. table.concat(parts, ", ") .. " }"
    elseif kind == "Closure" then
        return "nil"
    elseif kind == "ClassShape" then
        return "nil"
    end

    return "nil"
end

function lit.property(base, field)
    if lit.identifier(field) then
        return base .. "." .. field
    end
    return base .. "[" .. lit.string(field or "?") .. "]"
end

return lit
]===],
    ["main.passes.conditions"] = [===[
local ins = require("main.bytecode.instructions")

local pass = {}

function pass.run(ir)
    local out = {}
    for _, n in ipairs(ir.ops) do
        if ins.isConditional(n.op) then
            out[n.pc] = {
                jump = ins.jumpTarget(n.pc, n.op),
                fall = ins.next(ir.proto, n.pc, ir.cfg.aux),
                block = n.block,
                join = ir.cfg.ipdom[n.block],
            }
        end
    end
    ir.conds = out
    return ir
end

return pass
]===],
    ["main.passes.constants"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local pass = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kval(k)
    if not k then return nil, true end
    local t = k.__type
    if t == "Nil" then return nil, true end
    if t == "Boolean" or t == "Number" then return k.Value, true end
    if t == "Integer" then
        local v = k.Value
        if k.IsNegative and type(v) == "number" and v > 0 then v = -v end
        return v, true
    end
    if t == "String" then return lit.rawStringConstant(k), true end
    return nil, false
end

local function text(v)
    local t = type(v)
    if v == nil then return "nil" end
    if t == "string" then return lit.string(v) end
    if t == "boolean" then return tostring(v) end
    if t == "number" then return lit.number(v) end
    return nil
end

local function truth(v)
    return v ~= nil and v ~= false
end

local function calc(op, a, b)
    local ok, out = pcall(function()
        if op == "ADD" or op == "ADDK" then return a + b end
        if op == "SUB" or op == "SUBK" then return a - b end
        if op == "MUL" or op == "MULK" then return a * b end
        if op == "DIV" or op == "DIVK" then return a / b end
        if op == "MOD" or op == "MODK" then return a % b end
        if op == "POW" or op == "POWK" then return a ^ b end
        if op == "IDIV" or op == "IDIVK" then return math.floor(a / b) end
        if op == "SUBRK" then return a - b end
        if op == "DIVRK" then return a / b end
        if op == "AND" or op == "ANDK" then return truth(a) and b or a end
        if op == "OR" or op == "ORK" then return truth(a) and a or b end
    end)
    return ok and out or nil, ok
end

function pass.run(ir)
    ir.constval = {}

    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local defs = ir.ssa.defsByPC[n.pc]
        local id = defs and defs[op.A] and ir:resolve(defs[op.A]) or nil
        local v, known = nil, false

        if name == "LOADNIL" then v, known = nil, true
        elseif name == "LOADB" then v, known = op.B == 1, true
        elseif name == "LOADN" then v, known = op.D, true
        elseif name == "LOADK" then v, known = kval(getk(ir.proto, op.D))
        elseif name == "LOADKX" then v, known = kval(getk(ir.proto, op.AuxValue and op.AuxValue.Value or 0))
        elseif name == "MOVE" then
            local src = ir:use(n.pc, op.B)
            if src and ir.constval[src] ~= nil then v, known = ir.constval[src].v, true
            elseif src and ir.constval[src] and ir.constval[src].nilv then v, known = nil, true end
        elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
            local src = ir:use(n.pc, op.B)
            local cv = src and ir.constval[src]
            if cv then
                local a = cv.nilv and nil or cv.v
                if name == "NOT" then v, known = not truth(a), true
                elseif name == "MINUS" and type(a) == "number" then v, known = -a, true
                elseif name == "LENGTH" and type(a) == "string" then v, known = #a, true end
            end
        elseif name == "CONCAT" then
            local out = {}
            known = true
            for r = op.B, op.C do
                local cv = ir.constval[ir:use(n.pc, r)]
                local x = cv and not cv.nilv and cv.v or nil
                if not cv or (type(x) ~= "string" and type(x) ~= "number") then known = false break end
                out[#out + 1] = tostring(x)
            end
            if known then v = table.concat(out) end
        else
            local rr = {
                ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true, IDIV = true,
                AND = true, OR = true,
            }
            local rk = {
                ADDK = true, SUBK = true, MULK = true, DIVK = true, MODK = true, POWK = true, IDIVK = true,
                ANDK = true, ORK = true,
            }
            if rr[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if av and bv then
                    v, known = calc(name, av.nilv and nil or av.v, bv.nilv and nil or bv.v)
                end
            elseif rk[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local b, bk = kval(getk(ir.proto, op.C))
                if av and bk then v, known = calc(name, av.nilv and nil or av.v, b) end
            elseif name == "SUBRK" or name == "DIVRK" then
                local a, ak = kval(getk(ir.proto, op.B))
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if ak and bv then v, known = calc(name, a, bv.nilv and nil or bv.v) end
            end
        end

        if id and known then
            ir.constval[id] = v == nil and { nilv = true } or { v = v }
            local s = text(v)
            if s then ir.const[id] = s end
        end
    end
    return ir
end

return pass
]===],
    ["main.passes.deadcode"] = [===[
local pass = {}

function pass.run(ir)
    local memo = {}
    local function live(id, seen)
        id = ir:resolve(id)
        if not id then return false end
        if memo[id] ~= nil then return memo[id] end
        seen = seen or {}
        if seen[id] then return false end
        seen[id] = true
        for _, u in ipairs(ir:uses(id) or {}) do
            if u.pc then
                memo[id] = true
                seen[id] = nil
                return true
            elseif u.phi and live(u.phi, seen) then
                memo[id] = true
                seen[id] = nil
                return true
            end
        end
        seen[id] = nil
        memo[id] = false
        return false
    end

    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and not live(id) then
            local pc = v.pc
            local op = pc and ir.bypc[pc]
            if op and (op.drop or ir.const[id] ~= nil) then ir.dead[id] = true end
        end
    end
    return ir
end

return pass
]===],
    ["main.passes.flow"] = [===[
local pass = {}

function pass.run(ir)
    ir.regions = {
        loops = ir.cfg.loops,
        ipdom = ir.cfg.ipdom,
        postdom = ir.cfg.postdom,
    }
    return ir
end

return pass
]===],
    ["main.passes.inline"] = [===[
local ins = require("main.bytecode.instructions")

local pass = {}

local function quiet(ir, a, b)
    local pc = ins.next(ir.proto, a, ir.cfg.aux)
    while pc < b do
        local n = ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = ins.next(ir.proto, pc, ir.cfg.aux)
    end
    return true
end

function pass.run(ir)
    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and v.kind == "def" then
            local u = ir:only(id)
            local n = v.pc and ir.bypc[v.pc]
            if u and u.pc and n and ir.cfg.blockmap[v.pc] == ir.cfg.blockmap[u.pc] then
                local useop = ir.bypc[u.pc]
                if n.pure and (not useop or useop.name ~= "CAPTURE") then
                    ir.inline[id] = true
                elseif n.name == "CALL" or n.name == "CALLFB" then
                    local nx = ins.next(ir.proto, v.pc, ir.cfg.aux)
                    if u.pc == nx or quiet(ir, v.pc, u.pc) then ir.inline[id] = true end
                end
            end
        end
    end
    for id in pairs(ir.const) do
        local ok = ir:count(id) > 0
        for _, u in ipairs(ir:uses(id) or {}) do
            local useop = u.pc and ir.bypc[u.pc] or nil
            if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
        end
        if ok then ir.inline[id] = true end
    end
    return ir
end

return pass
]===],
    ["main.passes.names"] = [===[
local pass = {}

function pass.run(ir)
    local parent = {}

    local function root(x)
        x = ir:resolve(x)
        if not x then return nil end
        local p = parent[x]
        if not p then parent[x] = x return x end
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end

    local function join(a, b)
        a, b = root(a), root(b)
        if a and b and a ~= b then parent[b] = a end
    end

    for id in pairs(ir.vals) do parent[id] = id end

    for _, phis in pairs(ir.phis) do
        for _, p in pairs(phis) do
            local pid = ir:resolve(p.id)
            if pid and not ir.dead[pid] and ir:count(pid) > 0 then
                for raw in pairs(p.inputs or {}) do join(pid, raw) end
            end
        end
    end

    local fam = {}
    for id in pairs(ir.vals) do fam[id] = root(id) end
    ir.family = fam
    return ir
end

return pass
]===],
    ["main.passes.pipeline"] = [===[
local simp = require("main.passes.simplify")
local konst = require("main.passes.constants")
local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt)
    opt = opt or {}
    simp.run(ir)
    if opt.fold ~= false then konst.run(ir) end
    if opt.dce ~= false then dead.run(ir) end
    names.run(ir)
    prov.run(ir)
    if opt.inline ~= false then inline.run(ir) end
    cond.run(ir)
    flow.run(ir)
    return ir
end

return pipe
]===],
    ["main.passes.provenance"] = [===[
local lit = require("main.output.literals")
local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local ty = require("main.naming.types")
local dbg = require("main.naming.debug_names")
local words = require("main.naming.words")
local ins = require("main.bytecode.instructions")

local pass = {}

local weak = {
    value = true, result = true, data = true, item = true, obj = true,
    num = true, text = true, flag = true, fn = true,
}

local owner = {
    Character = "player", Backpack = "player", PlayerGui = "player", PlayerScripts = "player",
    UserId = "player", Team = "player", TeamColor = "player", AccountAge = "player",
    Humanoid = "character", HumanoidRootPart = "character", PrimaryPart = "model",
    Health = "humanoid", MaxHealth = "humanoid", WalkSpeed = "humanoid", JumpPower = "humanoid",
    HipHeight = "humanoid", MoveDirection = "humanoid", FloorMaterial = "humanoid",
    CFrame = "part", Position = "part", Orientation = "part", Anchored = "part",
    CanCollide = "part", AssemblyLinearVelocity = "part", AssemblyAngularVelocity = "part",
    CameraType = "camera", CameraSubject = "camera", ViewportSize = "camera",
    AbsolutePosition = "gui", AbsoluteSize = "gui", BackgroundColor3 = "gui", Text = "gui",
    UserInputType = "input", KeyCode = "input", UserInputState = "input", Delta = "input",
    OnClientEvent = "remoteEvent", OnServerEvent = "remoteEvent",
}

local methown = {
    Kick = "player", GetMouse = "player", LoadCharacter = "player",
    MoveTo = "humanoid", TakeDamage = "humanoid", ChangeState = "humanoid",
    Raycast = "workspace", GetPartsInPart = "workspace", GetPartBoundsInBox = "workspace",
    Connect = "signal", ConnectParallel = "signal", Once = "signal", Wait = "signal",
    FireServer = "remoteEvent", FireClient = "remoteEvent", FireAllClients = "remoteEvent",
    InvokeServer = "remoteFunction", InvokeClient = "remoteFunction",
    GetPlayers = "players", GetPlayerFromCharacter = "players",
    GetTagged = "collectionService", HasTag = "collectionService", AddTag = "collectionService", RemoveTag = "collectionService",
    JSONDecode = "httpService", JSONEncode = "httpService", GenerateGUID = "httpService",
}

local function getk(proto, n)
    return proto.Constants and proto.Constants[(n or 0) + 1]
end

local function rawk(proto, n)
    return lit.rawStringConstant(getk(proto, n))
end

local function cv(ir, v)
    v = ir:resolve(v)
    local x = v and ir.constval and ir.constval[v]
    if not x then return nil, false end
    return x.nilv and nil or x.v, true
end

function pass.run(ir)
    local hints = {}
    local origin = {}
    local pend = {}
    local dr = dbg.ranges(ir.proto)
    local tr = ty.ranges(ir.proto)

    local function fam(v)
        return v and ir:nameid(v) or nil
    end

    local function add(v, name, score, why)
        v = fam(v)
        name = id.clean(name)
        if not v or not name then return end
        if weak[name] then score -= 8 end
        local h = hints[v]
        if not h then h = {}; hints[v] = h end
        local old = h[name]
        if not old then
            h[name] = { score = score, why = why, hits = 1 }
        else
            old.hits = (old.hits or 1) + 1
            if score > old.score then old.score, old.why = score, why end
        end
    end

    local function seto(v, path, kind)
        v = ir:resolve(v)
        if v and path then origin[v] = { path = path, kind = kind } end
    end

    local function geto(v)
        v = ir:resolve(v)
        return v and origin[v] or nil
    end

    local function opname(v)
        v = ir:resolve(v)
        local x = v and ir.vals[v]
        local n = x and x.pc and ir.bypc[x.pc]
        return n and n.name or nil
    end

    for v, src in pairs(ir.vals) do
        if src.kind == "param" and ir.paramhints then add(v, ir.paramhints[src.reg + 1], 118, "context") end
        local p = src.kind == "param" and ty.param(ir.proto, src.reg) or nil
        if p then add(v, ty.hint(p), 74, "ptype") end
        local di = src.pc and dbg.at(dr, src.reg, src.pc) or nil
        if di then add(v, di.name, 120, "debug") end
        local ti = src.pc and ty.at(tr, src.reg, src.pc) or nil
        if ti then add(v, ty.hint(ti), 78, "type") end
    end

    local prep = {}
    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local pc = n.pc
        local defs = ir.ssa.defsByPC[pc] or {}
        local uses = ir.ssa.usesByPC[pc] or {}
        local function d(r) return ir:resolve(defs[r]) end
        local function u(r) return ir:resolve(uses[r]) end

        if name == "GETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            add(d(op.A), g, 104, "global")
            seto(d(op.A), g, "global")
        elseif name == "GETIMPORT" then
            local k = getk(ir.proto, op.D)
            local p = lit.rawStringConstant(k) or lit.constant(k)
            add(d(op.A), rbx.fromImport(p) or words.call(p), 108, "import")
            seto(d(op.A), p, "import")
        elseif name == "GETUPVAL" then
            local up = ir.proto.Upvalues and ir.proto.Upvalues[op.B + 1]
            local un = up and up.Name
            add(d(op.A), un, 112, "upvalue")
            seto(d(op.A), un, "upvalue")
        elseif name == "MOVE" then
            local so = geto(u(op.B))
            if so then
                seto(d(op.A), so.path, so.kind)
                add(d(op.A), words.call(so.path) or words.field(so.path), 76, "move")
            end
        elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "GETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            add(d(op.A), rbx.fromField(f) or words.field(f), 91, "field")
            add(u(op.B), owner[f], 70, "owner")
            local so = geto(u(op.B))
            if so and f then seto(d(op.A), so.path .. "." .. f, "field") else seto(d(op.A), f, "field") end
        elseif name == "GETTABLEN" then
            local so = geto(u(op.B))
            if so then add(d(op.A), words.iter(words.call(so.path) or so.path), 64, "index") end
        elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "SETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 116 or 44
            add(u(op.A), rbx.fromField(f) or words.field(f), sc, "store")
        elseif name == "SETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 120 or 38
            add(u(op.A), g, sc, "gstore")
        elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "NAMECALLUDATA" then ai = bit32.band(ai, 0xffff) end
            local m = rawk(ir.proto, ai)
            pend[op.A] = { method = m, obj = u(op.B), pc = pc }
            add(u(op.B), methown[m], 72, "method-owner")
        elseif name == "CALL" or name == "CALLFB" then
            local p = pend[op.A]
            local out = d(op.A)
            local callpath
            if p then
                local arg
                if (op.B or 0) == 0 or op.B > 2 then arg = select(1, cv(ir, u(op.A + 2))) end
                local oo = geto(p.obj)
                local base = oo and oo.path or nil
                local h = rbx.fromMethod(p.method, arg) or words.method(p.method)
                if p.method == "Create" and base and base:match("TweenService$") then h = "tween" end
                if p.method == "Clone" and base then
                    local tail = base:match("([%a_][%w_]*)$")
                    if tail then h = words.clean(tail .. "Clone") end
                end
                if p.method == "Connect" or p.method == "ConnectParallel" or p.method == "Once" then h = "connection" end
                if p.method == "Wait" and base and base:match("Signal$") then h = "value" end
                add(out, h, 106, "method")
                if p.method == "GetPlayerFromCharacter" then
                    add(u(op.A + 2), "character", 88, "arg")
                elseif p.method == "Create" and base and base:match("TweenService$") then
                    add(u(op.A + 2), "instance", 62, "arg")
                    add(u(op.A + 3), "tweenInfo", 78, "arg")
                    add(u(op.A + 4), "properties", 72, "arg")
                elseif p.method == "Raycast" then
                    add(u(op.A + 2), "origin", 66, "arg")
                    add(u(op.A + 3), "direction", 72, "arg")
                    add(u(op.A + 4), "params", 58, "arg")
                elseif p.method == "AddTag" or p.method == "RemoveTag" or p.method == "HasTag" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "tag", 72, "arg")
                elseif p.method == "AddItem" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "lifetime", 68, "arg")
                end
                local path
                if p.method == "GetService" and arg then
                    path = tostring(arg)
                elseif (p.method == "WaitForChild" or p.method == "FindFirstChild" or p.method == "FindFirstAncestor") and arg then
                    path = base and (base .. "." .. tostring(arg)) or tostring(arg)
                elseif (p.method == "FindFirstChildOfClass" or p.method == "FindFirstChildWhichIsA") and arg then
                    path = tostring(arg)
                else
                    path = base
                    if p.method then path = path and (path .. ":" .. p.method) or p.method end
                end
                callpath = path
                seto(out, path, "call")
                pend[op.A] = nil
            else
                local cal = u(op.A)
                local co = geto(cal)
                local arg
                if (op.B or 0) == 0 or op.B > 1 then arg = select(1, cv(ir, u(op.A + 1))) end
                local path = co and co.path or nil
                local h = rbx.fromCall(path, arg) or words.call(path) or "result"
                local first = {
                    pcall = "success", xpcall = "success", ["coroutine.resume"] = "success",
                    next = "key", ["string.find"] = "startPos", ["math.modf"] = "integer",
                    ["math.frexp"] = "mantissa",
                }
                h = first[path] or h
                if path == "require" then
                    local ao = geto(u(op.A + 1))
                    local tail = ao and ao.path and ao.path:match("([%a_][%w_]*)$")
                    if tail and tail ~= "Parent" then h = words.clean(tail) end
                end
                callpath = path
                add(out, h, path == "require" and 112 or 98, "call")
                add(cal, "fn", 48, "callee")
                seto(out, path, "call")
                if path == "table.insert" then
                    add(u(op.A + 1), "list", 52, "arg")
                    add(u(op.A + 2), "item", 46, "arg")
                elseif path == "pairs" or path == "ipairs" or path == "next" then
                    add(u(op.A + 1), "items", 44, "arg")
                elseif path == "pcall" or path == "xpcall" then
                    add(u(op.A + 1), "fn", 66, "arg")
                elseif path == "task.spawn" or path == "task.defer" or path == "task.delay" then
                    local r = path == "task.delay" and op.A + 2 or op.A + 1
                    add(u(r), "callback", 68, "arg")
                elseif path == "assert" then
                    add(u(op.A + 1), "condition", 48, "arg")
                end
            end
            if (op.C or 0) > 2 then
                local multi = {
                    pcall = { "success", "result" },
                    xpcall = { "success", "result" },
                    ["coroutine.resume"] = { "success", "result" },
                    next = { "key", "value" },
                    ["string.find"] = { "startPos", "endPos" },
                    ["math.modf"] = { "integer", "fraction" },
                    ["math.frexp"] = { "mantissa", "exponent" },
                }
                local set = multi[callpath]
                for r = op.A, op.A + op.C - 2 do
                    local i = r - op.A + 1
                    local h = set and set[i] or (i == 1 and nil or ("result" .. tostring(i)))
                    if h then add(d(r), h, set and 96 or 35, "multi") end
                end
            end
        elseif name == "NEWTABLE" or name == "DUPTABLE" then
            add(d(op.A), "data", 28, "table")
            seto(d(op.A), "data", "table")
        elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = ir.proto.Protos and ir.proto.Protos[(op.D or 0) + 1]
            add(d(op.A), child and child.Name or "fn", 88, "closure")
        elseif name == "NOT" then
            local so = geto(u(op.B))
            if so then add(d(op.A), "not" .. ((words.call(so.path) or "value"):gsub("^%l", string.upper)), 52, "bool") end
        elseif name == "LENGTH" then
            local so = geto(u(op.B))
            if so then
                local x = words.call(so.path)
                if x then add(d(op.A), x .. "Count", 66, "len") else add(d(op.A), "count", 54, "len") end
            else
                add(d(op.A), "count", 48, "len")
            end
        elseif name == "FORGPREP" or name == "FORGPREP_NEXT" or name == "FORGPREP_INEXT" then
            local target = ins.jumpTarget(pc, op)
            local so = geto(u(op.A + 1)) or geto(u(op.A))
            prep[target] = so and (words.call(so.path) or words.field(so.path)) or nil
        elseif name == "FORGLOOP" then
            local nvar = math.max(1, bit32.band(op.AuxValue and op.AuxValue.Value or 0, 0xff))
            local src = prep[pc]
            for i = 1, nvar do
                local v = d(op.A + 2 + i)
                if i == 1 and nvar == 1 then add(v, words.iter(src), 86, "iter")
                elseif i == 1 then add(v, "key", 68, "iter")
                elseif i == 2 then add(v, words.iter(src) or "value", 82, "iter")
                else add(v, "value" .. tostring(i), 48, "iter") end
            end
        elseif name == "FORNLOOP" then
            add(d(op.A + 3), "i", 62, "numfor")
        end
    end

    for _, n in ipairs(ir.ops) do
        local op, pc, name = n.op, n.pc, n.name
        local uses = ir.ssa.usesByPC[pc] or {}
        local function u(r) return ir:resolve(uses[r]) end
        if name == "JUMPIF" or name == "JUMPIFNOT" then
            add(u(op.A), "enabled", 38, "condition")
        elseif name == "GETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "SETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "CONCAT" then
            for r = op.B, op.C do add(u(r), "text", 30, "concat") end
        elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
            add(u(op.B), "num", 24, "math")
            add(u(op.C), "num", 24, "math")
        end
    end

    local best, score = {}, {}
    for v, set in pairs(hints) do
        for name, h in pairs(set) do
            local rank = h.score + math.min(20, math.max(0, (h.hits or 1) - 1) * 4)
            if not score[v] or rank > score[v] or (rank == score[v] and name < best[v]) then
                best[v], score[v] = name, rank
            end
        end
    end

    ir.hints = hints
    ir.bestname = best
    ir.namescore = score
    ir.origin = origin
    return ir
end

return pass
]===],
    ["main.passes.simplify"] = [===[
local pass = {}

function pass.run(ir)
    local changed = true
    while changed do
        changed = false
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                if not ir.dead[p.id] and not p.missing then
                    local one
                    local many = false
                    for raw in pairs(p.inputs or {}) do
                        local id = ir:resolve(raw)
                        if id and id ~= p.id then
                            if one and one ~= id then many = true break end
                            one = id
                        end
                    end
                    if one and not many then
                        ir.alias[p.id] = one
                        ir.dead[p.id] = true
                        ir.vals[p.id].dead = true
                        changed = true
                    end
                end
            end
        end
    end
    ir:reindex()
    return ir
end

return pass
]===],
    ["main.recover.branches"] = [===[
local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local join = st:join(pc)
    if not join or join <= pc or join > stop then join = ch.exit end
    if ch.exit > join then return nil end

    if ch.exit == join then
        return { cond = ch.cond, a = ch.body, b = join, join = join }
    end

    return { cond = ch.cond, a = ch.body, b = ch.exit, c = ch.exit, d = join, join = join }
end

function branch.elseifInfo(st, pc, join)
    local op = st.proto.Instructions[pc]
    if not op or not ins.isConditional(op) then return nil end
    local sub = branch.info(st, pc, join)
    if sub and sub.join == join then return sub end
end

return branch
]===],
    ["main.recover.conditions"] = [===[
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")

local cond = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kexpr(proto, i)
    return ex.atom(lit.constant(getk(proto, i)), true)
end

function cond.jump(st, pc, op)
    local name = ins.name(op)
    local a = st:usex(pc, op.A)
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "JUMPIF" then return a end
    if name == "JUMPIFNOT" then return ex.un("not", a) end

    local b = st:usex(pc, bit32.band(aux, 0xff))
    local cmp = {
        JUMPIFEQ = "==", JUMPIFNOTEQ = "~=", JUMPIFLT = "<",
        JUMPIFLE = "<=", JUMPIFNOTLT = ">=", JUMPIFNOTLE = ">",
    }
    if cmp[name] then return ex.bin(a, cmp[name], b) end

    if name == "JUMPXEQKNIL" then
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", ex.atom("nil", true))
    elseif name == "JUMPXEQKB" then
        local v = bit32.band(aux, 1) == 1 and "true" or "false"
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", ex.atom(v, true))
    elseif name == "JUMPXEQKN" or name == "JUMPXEQKS" then
        local k = kexpr(st.proto, bit32.band(aux, 0xffffff))
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", k)
    end

    return ex.atom("true", true)
end

function cond.fall(st, pc, op)
    local name = ins.name(op)
    local a = st:usex(pc, op.A)
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "JUMPIF" then return ex.un("not", a) end
    if name == "JUMPIFNOT" then return a end

    local b = st:usex(pc, bit32.band(aux, 0xff))
    local cmp = {
        JUMPIFEQ = "~=", JUMPIFNOTEQ = "==", JUMPIFLT = ">=",
        JUMPIFLE = ">", JUMPIFNOTLT = "<", JUMPIFNOTLE = "<=",
    }
    if cmp[name] then return ex.bin(a, cmp[name], b) end

    if name == "JUMPXEQKNIL" then
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", ex.atom("nil", true))
    elseif name == "JUMPXEQKB" then
        local v = bit32.band(aux, 1) == 1 and "true" or "false"
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", ex.atom(v, true))
    elseif name == "JUMPXEQKN" or name == "JUMPXEQKS" then
        local k = kexpr(st.proto, bit32.band(aux, 0xffffff))
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", k)
    end

    return ex.un("not", cond.jump(st, pc, op))
end

function cond.chain(st, pc)
    local first = st.proto.Instructions[pc]
    if not ins.isConditional(first) then return nil end

    local exit = ins.jumpTarget(pc, first)
    local cur = pc
    local list = {}
    local count = 0

    while true do
        local op = st.proto.Instructions[cur]
        local name = ins.name(op)
        if not ins.isConditional(op) or name == "FORNLOOP" or name == "FORGLOOP" then break end
        if ins.jumpTarget(cur, op) ~= exit then break end
        list[#list + 1] = cond.fall(st, cur, op)
        count += 1
        local nx = st:next(cur)
        local nop = st.proto.Instructions[nx]
        if not nop or not ins.isConditional(nop) then
            return { cond = ex.join(list, "and"), body = nx, exit = exit, last = cur }
        end
        if ins.jumpTarget(nx, nop) ~= exit then break end
        cur = nx
    end

    if count > 1 then
        return { cond = ex.join(list, "and"), body = st:next(cur), exit = exit, last = cur }
    end

    local body = exit
    local p = pc
    local ors = {}
    while p < body do
        local op = st.proto.Instructions[p]
        if not op or not ins.isConditional(op) then break end
        local nx = st:next(p)
        local jt = ins.jumpTarget(p, op)
        if jt == body and nx < body then
            ors[#ors + 1] = cond.jump(st, p, op)
            p = nx
        elseif nx == body and jt > body then
            ors[#ors + 1] = cond.fall(st, p, op)
            return { cond = ex.join(ors, "or"), body = body, exit = jt, last = p }
        else
            break
        end
    end

    return { cond = cond.fall(st, pc, first), body = st:next(pc), exit = exit, last = pc }
end

function cond.bool(st, pc, op)
    if not ins.isConditional(op) then return nil end
    local fp = st:next(pc)
    local tp = ins.jumpTarget(pc, op)
    local fo = st.proto.Instructions[fp]
    local to = st.proto.Instructions[tp]
    if not fo or not to or ins.name(fo) ~= "LOADB" or ins.name(to) ~= "LOADB" or fo.A ~= to.A then return nil end

    local x
    if fo.B == 0 and to.B == 1 then
        x = cond.jump(st, pc, op)
    elseif fo.B == 1 and to.B == 0 then
        x = cond.fall(st, pc, op)
    else
        return nil
    end

    local join
    if fo.C ~= 0 then join = fp + fo.C + 1 else join = st:next(fp) end
    if join <= tp then join = st:next(tp) end
    st.consumed[fp] = true
    st.consumed[tp] = true
    local bid = st.cfg.blockmap[join]
    local phis = bid and st.ir.phis[bid]
    local phi = phis and phis[fo.A]
    if phi and not phi.missing then
        local id = st.ir:resolve(phi.id)
        st.vals[id] = x
        st.expr[id] = x
    else
        st:set(fp, fo.A, x)
    end
    return join
end

return cond
]===],
    ["main.recover.functions"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local fn = {}

local evt = {
    PlayerAdded = { "player" }, PlayerRemoving = { "player" },
    CharacterAdded = { "character" }, CharacterRemoving = { "character" },
    ChildAdded = { "child" }, ChildRemoved = { "child" },
    DescendantAdded = { "descendant" }, DescendantRemoving = { "descendant" },
    Touched = { "hit" }, TouchEnded = { "hit" },
    InputBegan = { "input", "gameProcessed" }, InputChanged = { "input", "gameProcessed" }, InputEnded = { "input", "gameProcessed" },
    Heartbeat = { "dt" }, RenderStepped = { "dt" }, PreRender = { "dt" }, PreSimulation = { "dt" }, PostSimulation = { "dt" },
    Stepped = { "time", "dt" },
    AncestryChanged = { "child", "parent" }, AttributeChanged = { "attribute" },
    Changed = { "value" },
}

local meth = {
    BindToRenderStep = { "dt" },
    BindAction = { "actionName", "inputState", "input" },
    BindActionAtPriority = { "actionName", "inputState", "input" },
}

local function cbhints(st, pc, r)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local call
    for _, u in ipairs(st.ir:uses(v) or {}) do
        if u.pc then
            if call then return nil end
            call = u.pc
        end
    end
    if not call then return nil end
    local op = st.proto.Instructions[call]
    local name = ins.name(op)
    if name ~= "CALL" and name ~= "CALLFB" then return nil end
    local pend = st.namecall[op.A]
    if pend and (pend.method == "Connect" or pend.method == "ConnectParallel" or pend.method == "Once") then
        local tail = pend.obj and pend.obj:match("([%a_][%w_]*)$")
        return tail and evt[tail] or nil
    end
    if pend and meth[pend.method] then return meth[pend.method] end
    return nil
end

function fn.caps(st, pc, child)
    local out = {}
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        local du = child.Upvalues and child.Upvalues[i]
        local dn = du and du.Name
        if ins.name(op) ~= "CAPTURE" then
            out[i] = dn or ("upvalue" .. tostring(i - 1))
        else
            local kind, src = op.A, op.B
            if dn and dn ~= "" then out[i] = dn
            elseif kind == 0 or kind == 1 then out[i] = st:useName(cp, src, nil)
            else out[i] = st.up[src + 1] or ("upvalue" .. tostring(src)) end
            st.consumed[cp] = true
            nx = st:next(cp)
        end
    end
    return out, nx
end

local function direct(st, pc, r, nx)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local uses = st.ir:uses(v) or {}
    local one
    for _, u in ipairs(uses) do
        if u.pc then
            if one then return nil end
            one = u
        end
    end
    if not one or one.pc ~= nx then return nil end
    local op = st.proto.Instructions[one.pc]
    local name = ins.name(op)
    if name == "SETGLOBAL" and op.A == r then
        local k = op.AuxValue and op.AuxValue.Value or 0
        local g = lit.rawStringConstant(st.proto.Constants and st.proto.Constants[k + 1])
        if g and lit.identifier(g) then return g, false, one.pc end
    elseif (name == "SETTABLEKS" or name == "SETUDATAKS") and op.A == r then
        local k = op.AuxValue and op.AuxValue.Value or 0
        if name == "SETUDATAKS" then k = bit32.band(k, 0xffff) end
        local f = lit.rawStringConstant(st.proto.Constants and st.proto.Constants[k + 1])
        local base = st:use(one.pc, op.B)
        if f and lit.identifier(f) then return base .. "." .. f, false, one.pc end
        if f then return lit.property(base, f), true, one.pc end
    end
end

function fn.emit(d, st, pc, r, child, caps, nx)
    local hint = child.Name
    if hint == nil or hint == "" then hint = st.ir.bestname and st.ir.bestname[st.ir:nameid(st:verdef(pc, r))] end
    if hint == nil or hint == "" then hint = "fn" .. tostring(r) end

    local root, sub, args = d:_child(child, caps, cbhints(st, pc, r))
    local target, assign, store = direct(st, pc, r, nx or st:next(pc))
    if target then
        st.consumed[store] = true
        if not assign and target:find("%.") and args[1] and args[1]:match("^self%s*[:$]") then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then
                target = base .. ":" .. field
                table.remove(args, 1)
            end
        elseif not assign and target:find("%.") and args[1] == "self" then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then
                target = base .. ":" .. field
                table.remove(args, 1)
            end
        end
        st.ast:add({ kind = "function", name = target, args = table.concat(args, ", "), body = root, localfn = false, assign = assign })
    else
        local name = st:defName(pc, r, hint)
        local depth = st.declared[name]
        if depth == nil or depth > st.indent then
            st.declared[name] = st.indent
            st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = true, assign = false })
        else
            st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = false, assign = true })
        end
    end
    for _, issue in ipairs(sub.bad) do st.bad[#st.bad + 1] = issue end
end

return fn
]===],
    ["main.recover.guards"] = [===[
local pass = {}

local function term(block)
    local body = block and block.body
    local last = body and body[#body]
    return last and (last.kind == "return" or last.kind == "break" or last.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.branches[1].body) then
                local rest = node.elsebody.body
                node.elsebody = nil
                out[#out + 1] = node
                for _, sub in ipairs(rest) do out[#out + 1] = sub end
            else
                out[#out + 1] = node
            end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.recover.loops"] = [===[
local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local loops = {}

function loops.whileInfo(st, pc)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local latch = ins.previousRealPC(st.cfg.aux, ch.exit)
    if not latch then return nil end
    local op = st.proto.Instructions[latch]
    local name = ins.name(op)
    if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(latch, op) <= pc then
        return { cond = ch.cond, body = ch.body, bodyend = latch, exit = ch.exit, cont = pc }
    end
end

function loops.repeatInfo(st, pc)
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc then
            local op = st.proto.Instructions[loop.latchPC]
            if ins.isConditional(op) and ins.jumpTarget(loop.latchPC, op) == pc then
                return { body = pc, latch = loop.latchPC, exit = st:next(loop.latchPC), cont = loop.latchPC }
            end
        end
    end
end

function loops.foreverInfo(st, pc, stop)
    local head = st.proto.Instructions[pc]
    if ins.isConditional(head) then return nil end
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc and loop.latchPC < stop then
            local op = st.proto.Instructions[loop.latchPC]
            local name = ins.name(op)
            if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(loop.latchPC, op) == pc then
                local exit = loop.exitPC
                if not exit then
                    for _, ep in ipairs(loop.exits or {}) do
                        if ep > loop.latchPC and (not exit or ep < exit) then exit = ep end
                    end
                end
                exit = exit or st:next(loop.latchPC)
                return { body = pc, latch = loop.latchPC, exit = exit, cont = pc }
            end
        end
    end
end

function loops.numInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORNLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

function loops.genInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORGLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

return loops
]===],
    ["main.recover.tables"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")
local ex = require("main.output.expr")

local tab = {}

local function key(k)
    local raw = lit.rawStringConstant(k)
    if raw then
        if lit.identifier(raw) then return "field", raw end
        return "key", lit.string(raw)
    end
    return "key", lit.constant(k)
end

function tab.seed(k)
    local out, slots = {}, {}
    if not k then return out, slots end
    if k.__type == "Table" then
        for _, x in ipairs(k.Value or {}) do
            local kind, name = key(x)
            local e = { kind = kind, key = name, pending = true }
            out[#out + 1] = e
            if kind == "field" then slots[name] = e end
        end
    elseif k.__type == "TableWithConstants" then
        for _, pair in ipairs(k.Value or {}) do
            local kind, name = key(pair.Key)
            local e = { kind = kind, key = name, pending = pair.Value == nil }
            if pair.Value ~= nil then e.val = ex.atom(lit.constant(pair.Value), true) end
            out[#out + 1] = e
            if kind == "field" then slots[name] = e end
        end
    end
    return out, slots
end

function tab.put(t, kind, name, val)
    local e = kind == "field" and t.slots and t.slots[name] or nil
    if e and e.pending then
        e.val = val
        e.pending = false
        return true
    end
    t.entries[#t.entries + 1] = { kind = kind, key = name, val = val }
    return true
end

function tab.mut(st, use, r)
    if not use or not use.pc then return false end
    local op = st.proto.Instructions[use.pc]
    local name = op and ins.name(op)
    if name == "SETTABLE" or name == "SETTABLEKS" or name == "SETUDATAKS" or name == "SETTABLEN" then
        return op.B == r
    elseif name == "SETLIST" then
        return op.A == r
    end
    return false
end

function tab.expr(t)
    local out = {}
    for _, e in ipairs(t.entries) do
        if not e.pending and e.val then
            if e.kind == "list" then
                out[#out + 1] = ex.str(e.val)
            elseif e.kind == "field" then
                out[#out + 1] = e.key .. " = " .. ex.str(e.val)
            else
                out[#out + 1] = "[" .. e.key .. "] = " .. ex.str(e.val)
            end
        end
    end
    return ex.atom(#out == 0 and "{}" or ("{ " .. table.concat(out, ", ") .. " }"), false)
end

function tab.use(st, v, r, pc)
    local t = st.tbl[v]
    if not t or t.done then return nil end
    t.done = true
    local node = tab.expr(t)
    if t.real <= 1 then return node end
    local name = st:useName(pc, r, nil)
    local depth = st.declared[name]
    if depth ~= nil and depth <= st.indent then
        st:out(name .. " = " .. ex.str(node))
    else
        st.declared[name] = st.indent
        st:out("local " .. name .. " = " .. ex.str(node))
    end
    return ex.atom(name, false)
end

return tab
]===],
    ["main.runtime.bytecode"] = [===[
local bc = {}

function bc.fromScript(obj)
    assert(typeof(obj) == "Instance", "LumenDecomp: target must be a Roblox Instance")
    assert(type(getscriptbytecode) == "function",
        "LumenDecomp: executor does not expose getscriptbytecode()")

    local ok, raw = pcall(getscriptbytecode, obj)
    if not ok then
        error("LumenDecomp: getscriptbytecode failed: " .. tostring(raw), 2)
    end

    local ty = typeof(raw)
    assert(type(raw) == "string" or ty == "buffer",
        "LumenDecomp: getscriptbytecode returned unsupported type " .. tostring(ty))

    return raw
end

return bc
]===],
    ["main.runtime.core"] = [===[
local core = {}

local roots = {
    Chat = true,
    CoreGui = true,
    CorePackages = true,
    RobloxReplicatedStorage = true,
    CoreScriptSyncService = true,
}

local player = {
    PlayerModule = true,
    RbxCharacterSounds = true,
    ChatScript = true,
    BubbleChat = true,
    PlayerScriptsLoader = true,
}

function core.root(obj)
    return obj and (roots[obj.Name] == true or roots[obj.ClassName] == true) or false
end

function core.is(obj)
    local cur = obj
    while cur and cur ~= game do
        if core.root(cur) then return true end
        if player[cur.Name] then
            local p = cur.Parent
            if p and (p.Name == "PlayerScripts" or p.Name == "StarterPlayerScripts") then
                return true
            end
        end
        cur = cur.Parent
    end
    return false
end

return core
]===],
    ["main.runtime.environment"] = [===[
local env = {}

function env.get()
    if type(getgenv) == "function" then
        local ok, e = pcall(getgenv)
        if ok and type(e) == "table" then
            return e
        end
    end

    if type(getfenv) == "function" then
        local ok, e = pcall(getfenv, 0)
        if ok and type(e) == "table" then
            return e
        end
    end

    return _G
end

function env.request()
    local e = env.get()

    return rawget(e, "request")
        or rawget(e, "http_request")
        or (type(syn) == "table" and syn.request)
end

return env
]===],
    ["main.runtime.http"] = [===[
local env = require("main.runtime.environment")

local http = {}

function http.get(url)
    local ok, body = pcall(function()
        return game:HttpGet(url)
    end)

    if ok and type(body) == "string" and #body > 0 then
        return body
    end

    local req = env.request()
    if type(req) == "function" then
        local rok, res = pcall(req, {
            Url = url,
            Method = "GET",
        })

        if rok and type(res) == "table" then
            local body = res.Body or res.body
            local code = res.StatusCode or res.Status or res.code

            if type(body) == "string"
                and #body > 0
                and (code == nil or (code >= 200 and code < 300)) then
                return body
            end
        end
    end

    error("LumenDecomp: HTTP GET failed for " .. tostring(url), 2)
end

return http
]===],
    ["main.runtime.iridium"] = [===[
local env = require("main.runtime.environment")
local http = require("main.runtime.http")
local patch = require("main.runtime.iridium_patch")

local iri = {}

local owner = "ActualMasterOogway"
local repo = "Iridium"
local commit = "2a834af6c6f72918a9222eb4ac6b258e4c6cd4bf"
local rawBase = "https://raw.githubusercontent.com/" .. owner .. "/" .. repo .. "/" .. commit .. "/"

local cache = {}
local NIL = {}
local LOADING = {}
local root = nil

local function resolve(name)
    if name == "@root" then
        return "Src/init.luau"
    end

    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end

    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local req

req = function(name)
    local path = resolve(name)
    local hit = cache[path]

    if hit == LOADING then
        error("LumenDecomp: cyclic Iridium dependency at " .. path, 2)
    elseif hit ~= nil then
        return hit == NIL and nil or hit
    end

    cache[path] = LOADING

    local ok, value = pcall(function()
        local src = http.get(rawBase .. path)
        src = patch.apply(path, src)
        src = "local require = __LUMEN_IRIDIUM_REQUIRE\n" .. src

        local chunk, err = loadstring(src, "@Iridium/" .. path)
        if not chunk then
            error("LumenDecomp: failed compiling Iridium/" .. path .. ": " .. tostring(err), 0)
        end

        return chunk()
    end)

    if not ok then
        cache[path] = nil
        error("LumenDecomp: failed loading Iridium/" .. path .. ": " .. tostring(value), 2)
    end

    cache[path] = value == nil and NIL or value
    return value
end

function iri.get()
    if root then
        return root
    end

    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local e = env.get()
    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)

    e[key] = req
    local ok, value = pcall(req, "@root")

    if old == nil then
        e[key] = nil
    else
        e[key] = old
    end

    if not ok then
        error(value, 2)
    end

    assert(type(value) == "table" and type(value.Deserialize) == "function",
        "LumenDecomp: Iridium root did not expose Deserialize")

    root = value
    return root
end

function iri.info()
    local pi = patch.info()
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
    }
end

return iri
]===],
    ["main.runtime.iridium_patch"] = [===[
local patch = {}

local rev = "v13-3"

local function rep(s, a, b, tag)
    local p = s:find(a, 1, true)
    if not p then error("LumenDecomp: Iridium patch mismatch: " .. tag, 3) end
    return s:sub(1, p - 1) .. b .. s:sub(p + #a)
end

function patch.apply(path, src)
    src = src:gsub("\r\n", "\n"):gsub("\r", "\n")
    if path == "Src/Luau/Spec.luau" then
        src = rep(src, "LBC_VERSION_MAX = 11", "LBC_VERSION_MAX = 13", "spec.max")
        src = rep(src, "LBC_VERSION_TARGET = 6", "LBC_VERSION_TARGET = 9", "spec.target")
        src = rep(src, "    LBC_VERSION_TARGET = 9,\n", "    LBC_VERSION_TARGET = 9,\n    LBC_VERSION_CLASSES = 100,\n", "spec.classes")
        src = rep(src, "    LBC_CONSTANT_CLASS_SHAPE = 10,\n", "    LBC_CONSTANT_CLASS_SHAPE = 10,\n    LBC_CONSTANT_VECTORD = 11,\n", "spec.vectord")
        src = rep(src, [[    LOP__COUNT = { Index = 88, Name = "_COUNT", HasAux = false },]], [[    LOP_CMPPROTO = { Index = 88, Name = "CMPPROTO", HasAux = true },
    LOP_NEWCLASS = { Index = 89, Name = "NEWCLASS", HasAux = true },
    LOP__COUNT = { Index = 90, Name = "_COUNT", HasAux = false },]], "spec.v12ops")
        return src
    end

    if path == "Src/init.luau" then
        src = rep(src, [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX}, got {self.BytecodeVersion})`)
    end]], [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and self.BytecodeVersion ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX} or classes, got {self.BytecodeVersion})`)
    end]], "init.classes")

        src = rep(src, [[    for i = 1, self.ProtoCount do
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
    end]], [[    self.ProtoSizes = {}
    for i = 1, self.ProtoCount do
        local ProtoSize = nil
        local ProtoStart = nil
        if self.BytecodeVersion >= 12 then
            ProtoSize = Bytecode:ReadVarInt()
            ProtoStart = Bytecode.Offset
            self.ProtoSizes[i] = ProtoSize
        end
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
        if ProtoSize then
            local ProtoEnd = ProtoStart + ProtoSize
            if Bytecode.Offset < ProtoEnd then
                Bytecode:seek(ProtoEnd - Bytecode.Offset)
            elseif Bytecode.Offset > ProtoEnd then
                error(`Proto {i} overread ({Bytecode.Offset - ProtoEnd} bytes)`)
            end
        end
    end]], "init.sizes")

        src = rep(src, [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    if Version >= 12 then
        local ProtoSize = Bytecode:ReadVarInt()
        Bytecode:seek(ProtoSize)
        return
    end

    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], "init.skiphead")

        src = rep(src, [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        end]], [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        elseif Kind == 11 then
            Bytecode:seek(32)
        end]], "init.vectord")



        src = rep(src, [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
            return nil
        end]], [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and Version ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
            return nil
        end]], "init.probeclasses")

        src = rep(src, [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        Bytecode:seek(4)]], [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        if Version >= 12 then
            Bytecode:ReadVarInt()
        end

        Bytecode:seek(4)]], "init.probe")
        return src
    end

    if path == "Src/Classes/Proto.luau" then
        src = rep(src, [[        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], [[        elseif ConstantType == LuauSpec.LuauBytecodeConstants.LBC_CONSTANT_VECTORD then
            local x, y, z, w =
                Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64()
            self.Constants[ConstantIndex] = Vector.new(x, y, z, w)
        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], "proto.vectord")

        local cost = [[    if Deserializer.BytecodeVersion >= 12 and bit32.band(self.Flags or 0, 8) ~= 0 then
        self.Cost = Bytecode:ReadVarInt64()
    end
]]
        local mark = "\n\treturn self\nend\n\nexport type Proto"
        local pos = src:find(mark, 1, true)
        if not pos then
            mark = "\n    return self\nend\n\nexport type Proto"
            pos = src:find(mark, 1, true)
        end
        if not pos then error("LumenDecomp: Iridium patch mismatch: proto.cost", 3) end
        src = src:sub(1, pos) .. cost .. src:sub(pos + 1)
        return src
    end

    return src
end

function patch.info()
    return { rev = rev, max = 13, target = 9, classes = 100 }
end

return patch
]===],
    ["main.runtime.status"] = [===[
local st = {}

local gui
local text
local dead = false
local lastui = 0
local lastcon = 0

local function parent()
    if type(gethui) == "function" then
        local ok, out = pcall(gethui)
        if ok and out then return out end
    end

    local ok, out = pcall(function()
        return game:GetService("CoreGui")
    end)
    if ok then return out end
end

local function make()
    if gui and gui.Parent then return true end

    local p = parent()
    if not p then return false end

    local ok = pcall(function()
        gui = Instance.new("ScreenGui")
        gui.Name = "LumenStatus"
        gui.ResetOnSpawn = false
        gui.IgnoreGuiInset = true
        gui.DisplayOrder = 2147483647

        local box = Instance.new("Frame")
        box.Name = "Box"
        box.AnchorPoint = Vector2.new(0.5, 0)
        box.Position = UDim2.new(0.5, 0, 0, 12)
        box.Size = UDim2.new(0, 760, 0, 54)
        box.BackgroundColor3 = Color3.fromRGB(14, 14, 17)
        box.BackgroundTransparency = 0.08
        box.BorderSizePixel = 0
        box.Parent = gui

        local corner = Instance.new("UICorner")
        corner.CornerRadius = UDim.new(0, 8)
        corner.Parent = box

        text = Instance.new("TextLabel")
        text.Name = "Text"
        text.BackgroundTransparency = 1
        text.Position = UDim2.new(0, 14, 0, 5)
        text.Size = UDim2.new(1, -28, 1, -10)
        text.Font = Enum.Font.Code
        text.TextColor3 = Color3.fromRGB(245, 245, 245)
        text.TextSize = 15
        text.TextXAlignment = Enum.TextXAlignment.Left
        text.TextYAlignment = Enum.TextYAlignment.Center
        text.TextWrapped = true
        text.Text = "LumenDecomp"
        text.Parent = box

        gui.Parent = p
    end)

    return ok
end

function st.path(obj)
    if not obj then return "" end
    local ok, out = pcall(function()
        return obj:GetFullName()
    end)
    return ok and out or tostring(obj)
end

local function msg(stage, obj, done, total, rate)
    local path = type(obj) == "string" and obj or st.path(obj)
    local count = ""
    if done and total then
        count = " [" .. tostring(done) .. "/" .. tostring(total) .. "]"
    end
    if rate then
        count = count .. " " .. string.format("%.1f/s", rate)
    end
    local out = "LumenDecomp - " .. tostring(stage) .. count
    if path ~= "" then out = out .. "\n" .. path end
    return out
end

local function show(out, console)
    if dead then return end
    if make() and text then text.Text = out end
    if console and type(rconsoleprint) == "function" then
        pcall(rconsoleprint, out .. "\n")
    end
end

function st.set(stage, obj, done, total)
    local out = msg(stage, obj, done, total)
    show(out, true)
    lastui = os.clock()
    lastcon = lastui
end

function st.progress(stage, obj, done, total, rate)
    if dead then return end
    local now = os.clock()
    if done ~= total and now - lastui < 0.075 then return end
    local out = msg(stage, obj, done, total, rate)
    local con = done == total or now - lastcon >= 0.5
    show(out, con)
    lastui = now
    if con then lastcon = now end
end

function st.done(msgtext)
    st.set(msgtext or "Done")
    if gui then
        task.delay(5, function()
            if gui then pcall(function() gui:Destroy() end) end
            gui = nil
            text = nil
        end)
    end
end

function st.kill()
    dead = true
    if gui then pcall(function() gui:Destroy() end) end
    gui = nil
    text = nil
end

return st
]===],
    ["main.serialization.dex_serializer"] = [===[
--[[

    ____               _____           _       ___                
   / __ \___  _  __   / ___/___  _____(_)___ _/ (_)___  ___  _____
  / / / / _ \| |/_/   \__ \/ _ \/ ___/ / __ `/ / /_  / / _ \/ ___/
 / /_/ /  __/>  <    ___/ /  __/ /  / / /_/ / / / / /_/  __/ /    
/_____/\___/_/|_|   /____/\___/_/  /_/\__,_/_/_/ /___/\___/_/     
                                                                  

The most accurate and top lua roblox binary format serializer since late 2020

Made in preparation for The Augur's reign that started in July 2021

Many ServerScriptService and ServerStorage models of top games were saved with top accuracy


This is old and discontinued, but the agency released it to show people the grand serializer that
powered the saveinstance function in the top executors at the time before they were discontinued:
- ScriptWare
- Synapse X


It would be nice if someone forked and improved it
- Support the newer types
- Use buffer
- Use ReflectionService


]]


-- Made by Moon
local Main,Serializer,API,Settings,DefaultSettings,env
local injectedDecompiler

local service = setmetatable({},{__index = function(self,name)
	local serv = game:GetService(name)
	self[name] = serv
	return serv
end})

DefaultSettings = {
	Serializer = {
		_Recurse = true,
		Decompile = false,
		NilInstances = false,
		RemovePlayerCharacters = true,
		SavePlayers = false,
		DecompileTimeout = 10,
		MaxThreads = 3,
		DecompileIgnore = {"Chat","CoreGui","CorePackages"},
		ShowStatus = true,
		IgnoreDefaultProps = true,
		IsolateStarterPlayer = true,
		Binary = true,
		Callback = false,
		Clipboard = false
	}
}

Serializer = (function()
	local Serializer = {}

	local oldIndex,getnspval,getbspval,gethiddenprop,getnilinstances,getpcd,encodeBase64,lz4compress,hashmd5
	local classes,saveProps,testInsts = {},{},{}
	local tostring = tostring
	local format = string.format
	local gsub = string.gsub
	local sub = string.sub
	local getChildren = game.GetChildren
	local isa = game.IsA
	local components = CFrame.new(0,0,0).GetComponents
	local httpService = service.HttpService
	local urlEncode = httpService.UrlEncode
	local concat = table.concat
	local s_pack = string.pack
	local s_unpack = string.unpack
	local lrotate = bit32.lrotate
	local tableCreate = table.create
	local select = select
	local unpack = unpack
	local split = string.split
	local s_rep = string.rep
	local nilSafe = {}
	local gameId

	--[[
	local propBypass = {
		["BasePart"] = {
			["Size"] = true,
			["Color"] = true,
		},
		["Part"] = {
			["Shape"] = true
		},
		["Fire"] = {
			["Heat"] = true,
			["Size"] = true,
		},
		["Smoke"] = {
			["Opacity"] = true,
			["RiseVelocity"] = true,
			["Size"] = true,
		},
		["DoubleConstrainedValue"] = {
			["Value"] = true
		},
		["IntConstrainedValue"] = {
			["Value"] = true
		},
		["TrussPart"] = {
			["Style"] = true
		}
	}
	]]
	local propBypass = {
		["BasePart"] = {
			["Color"] = true, -- No Coloruint8
		},
	}


	local propFilter = {
		["BaseScript"] = {
			["LinkedSource"] = true
		},
		["Script"] = {
			["Source"] = true
		},
		["ModuleScript"] = {
			["LinkedSource"] = true,
			["Source"] = true
		},
		["Players"] = {
			["CharacterAutoLoads"] = true
		},
		["BillboardGui"] = {
			["PlayerToHideFrom"] = true
		},
		["Instance"] = {
			["SourceAssetId"] = true,
			["PropertyStatusStudio"] = true
		},
		["Model"] = {
			["WorldPivotData"] = true -- No OptionalCoordinateFrame
		},
		["TerrainRegion"] = { -- No Vector3int16
			["ExtentsMax"] = true,
			["ExtentsMin"] = true
		}
	}

	local xmlReplacePattern = "['\"<>&\0]"

	local xmlReplace = {
		["'"] = "&apos;",
		["\""] = "&quot;",
		["<"] = "&lt;",
		[">"] = "&gt;",
		["&"] = "&amp;",
		["\0"] = ""
	}

	local serviceBlacklist = {
		["CoreGui"] = true,
		["CorePackages"] = true,
	}

	local nilClassParents = {
		["Attachment"] = "Part",
		["Bone"] = "Part",
		["Animator"] = "Humanoid",
		["SurfaceAppearance"] = "MeshPart"
	}

	local valueConverters = {
		["bool"] = function(name,val)
			return '\n<bool name="'..name..'">'..(val and "true" or "false")..'</bool>'
		end,
		["int"] = function(name,val)
			return format('\n<int name="%s">%d</int>',name,val)
		end,
		["int64"] = function(name,val)
			return format('\n<int64 name="%s">%d</int64>',name,val)
		end,
		["float"] = function(name,val)
			return format('\n<float name="%s">%.12f</float>',name,val)
		end,
		["double"] = function(name,val)
			return format('\n<double name="%s">%.12f</double>',name,val)
		end,
		["string"] = function(name,val)
			return '\n<string name="'..name..'">'..gsub(val,xmlReplacePattern,xmlReplace)..'</string>'
		end,
		["BrickColor"] = function(name,val)
			return format('\n<int name="%s">%d</int>',name,val.Number)
		end,
		["Vector2"] = function(name,val)
			return format('\n<Vector2 name="%s">\n<X>%.12f</X>\n<Y>%.12f</Y>\n</Vector2>',name,val.X,val.Y)
		end,
		["Vector3"] = function(name,val)
			return format('\n<Vector3 name="%s">\n<X>%.12f</X>\n<Y>%.12f</Y>\n<Z>%.12f</Z>\n</Vector3>',name,val.X,val.Y,val.Z)
		end,
		["Vector3int16"] = function(name,val)
			return format('\n<Vector3int16 name="%s">\n<X>%d</X>\n<Y>%d</Y>\n<Z>%d</Z>\n</Vector3int16>',name,val.X,val.Y,val.Z)
		end,
		["CFrame"] = function(name,val)
			return format('\n<CoordinateFrame name="%s">\n<X>%.12f</X>\n<Y>%.12f</Y>\n<Z>%.12f</Z>\n<R00>%.12f</R00>\n<R01>%.12f</R01>\n<R02>%.12f</R02>\n<R10>%.12f</R10>\n<R11>%.12f</R11>\n<R12>%.12f</R12>\n<R20>%.12f</R20>\n<R21>%.12f</R21>\n<R22>%.12f</R22>\n</CoordinateFrame>',name,components(val))
		end,
		["Content"] = function(name,val)
			if sub(val,1,15) == "rbxgameasset://" then
				val = format("https://assetdelivery.roblox.com/v1/asset?universeId=%d&assetName=%s&skipSigningScripts=1",gameId,urlEncode(httpService,sub(val,16)))
			end
			return '\n<Content name="'..name..'"><url>'..gsub(val,xmlReplacePattern,xmlReplace)..'</url></Content>'
		end,
		["UDim"] = function(name,val)
			return format('\n<UDim name="%s">\n<S>%.12f</S>\n<O>%d</O>\n</UDim>',name,val.Scale,val.Offset)
		end,
		["UDim2"] = function(name,val)
			local x = val.X
			local y = val.Y
			return format('\n<UDim2 name="%s">\n<XS>%.12f</XS>\n<XO>%d</XO>\n<YS>%.12f</YS>\n<YO>%d</YO>\n</UDim2>',name,x.Scale,x.Offset,y.Scale,y.Offset)
		end,
		["Color3"] = function(name,val)
			return format('\n<Color3 name="%s">\n<R>%.12f</R>\n<G>%.12f</G>\n<B>%.12f</B>\n</Color3>',name,val.R,val.G,val.B)
		end,
		["NumberRange"] = function(name,val)
			return '\n<NumberRange name="'..name..'">'..tostring(val)..'</NumberRange>'
		end,
		["NumberSequence"] = function(name,val)
			return '\n<NumberSequence name="'..name..'">'..tostring(val)..'</NumberSequence>'
		end,
		["ColorSequence"] = function(name,val)
			return '\n<ColorSequence name="'..name..'">'..tostring(val)..'</ColorSequence>'
		end,
		["Rect"] = function(name,val)
			local min,max = val.Min,val.Max
			return format('\n<Rect2D name="%s">\n<min>\n<X>%.12f</X>\n<Y>%.12f</Y>\n</min>\n<max>\n<X>%.12f</X>\n<Y>%.12f</Y>\n</max>\n</Rect2D>',name,min.X,min.Y,max.X,max.Y)
		end,
		["PhysicalProperties"] = function(name,val)
			if val then
				return format('\n<PhysicalProperties name="%s">\n<CustomPhysics>true</CustomPhysics>\n<Density>%.12f</Density>\n<Friction>%.12f</Friction>\n<Elasticity>%.12f</Elasticity>\n<FrictionWeight>%.12f</FrictionWeight>\n<ElasticityWeight>%.12f</ElasticityWeight>\n</PhysicalProperties>',name,val.Density,val.Friction,val.Elasticity,val.FrictionWeight,val.ElasticityWeight)
			else
				return '\n<PhysicalProperties name="'..name..'">\n<CustomPhysics>false</CustomPhysics>\n</PhysicalProperties>'
			end
		end,
		["Faces"] = function(name,val)
			local faceInt = (val.Front and 32 or 0) + (val.Bottom and 16 or 0) + (val.Left and 8 or 0) + (val.Back and 4 or 0) + (val.Top and 2 or 0) + (val.Right and 1 or 0)
			return format('\n<Faces name="%s">\n<faces>%d</faces>\n</Faces>',name,faceInt)
		end,
		["Axes"] = function(name,val)
			local axisInt = (val.Z and 4 or 0) + (val.Y and 2 or 0) + (val.X and 1 or 0)
			return format('\n<Axes name="%s">\n<axes>%d</axes>\n</Axes>',name,axisInt)
		end,
		["Ray"] = function(name,val)
			local origin = val.Origin
			local direction = val.Direction
			return format('\n<Ray name="%s">\n<origin>\n<X>%.12f</X>\n<Y>%.12f</Y>\n<Z>%.12f</Z>\n</origin>\n<direction>\n<X>%.12f</X>\n<Y>%.12f</Y>\n<Z>%.12f</Z>\n</direction>\n</Ray>',name,origin.X,origin.Y,origin.Z,direction.X,direction.Y,direction.Z)
		end,
		["BinaryString"] = function(name,val)
			if val then
				return '\n<BinaryString name="'..name..'"><![CDATA['..val..']]></BinaryString>'
			else
				return ""
			end
		end,
		["ProtectedString"] = function(name,val)
			return '\n<ProtectedString name="'..name..'">'..gsub(val,xmlReplacePattern,xmlReplace)..'</ProtectedString>'
		end,
		["SharedString"] = function(name,val)
			return '\n<SharedString name="'..name..'">'..val..'</SharedString>'
		end,
	}

	local binaryDataTypes = {
		["string"] = "\1",
		["ContentId"] = "\1",
		["Content"] = "\1", -- Lumen: newer API dump alias
		["BinaryString"] = "\1",
		["bool"] = "\2",
		["int"] = "\3",
		["float"] = "\4",
		["double"] = "\5",
		["UDim"] = "\6",
		["UDim2"] = "\7",
		["Ray"] = "\8",
		["Faces"] = "\9",
		["Axes"] = "\10",
		["BrickColor"] = "\11",
		["Color3"] = "\12",
		["Vector2"] = "\13",
		["Vector3"] = "\14",
		["CFrame"] = "\16",
		["Enum"] = "\18",
		["Referent"] = "\19",
		["Vector3int16"] = "\20",
		["NumberSequence"] = "\21",
		["ColorSequence"] = "\22",
		["NumberRange"] = "\23",
		["Rect"] = "\24",
		["PhysicalProperties"] = "\25",
		["Color3uint8"] = "\26",
		["int64"] = "\27",
		["SharedString"] = "\28",
		["OptionalCoordinateFrame"] = "\30",
		["Font"] = "\32"
	}

	local binaryCFrameMap = {
		["\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63"] = "\2",
		["\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\63\0\0\0\0"] = "\3",
		["\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191"] = "\5",
		["\0\0\128\63\0\0\0\0\0\0\0\128\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\191\0\0\0\0"] = "\6",
		["\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191"] = "\7",
		["\0\0\0\0\0\0\0\0\0\0\128\63\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0"] = "\9",
		["\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\128\0\0\0\0\0\0\0\0\0\0\128\63"] = "\10",
		["\0\0\0\0\0\0\0\0\0\0\128\191\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0"] = "\12",
		["\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\128\63\0\0\0\0\0\0\0\0"] = "\13",
		["\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0"] = "\14",
		["\0\0\0\0\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\128\63\0\0\0\0\0\0\0\0"] = "\16",
		["\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\128"] = "\17",
		["\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191"] = "\20",
		["\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\63\0\0\0\128"] = "\21",
		["\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63"] = "\23",
		["\0\0\128\191\0\0\0\0\0\0\0\128\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\191\0\0\0\128"] = "\24",
		["\0\0\0\0\0\0\128\63\0\0\0\128\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63"] = "\25",
		["\0\0\0\0\0\0\0\0\0\0\128\191\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0"] = "\27",
		["\0\0\0\0\0\0\128\191\0\0\0\128\0\0\128\191\0\0\0\0\0\0\0\128\0\0\0\0\0\0\0\0\0\0\128\191"] = "\28",
		["\0\0\0\0\0\0\0\0\0\0\128\63\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0"] = "\30",
		["\0\0\0\0\0\0\128\63\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\191\0\0\128\191\0\0\0\0\0\0\0\0"] = "\31",
		["\0\0\0\0\0\0\0\0\0\0\128\63\0\0\0\0\0\0\128\63\0\0\0\128\0\0\128\191\0\0\0\0\0\0\0\0"] = "\32",
		["\0\0\0\0\0\0\128\191\0\0\0\0\0\0\0\0\0\0\0\0\0\0\128\63\0\0\128\191\0\0\0\0\0\0\0\0"] = "\34",
		["\0\0\0\0\0\0\0\0\0\0\128\191\0\0\0\0\0\0\128\191\0\0\0\128\0\0\128\191\0\0\0\0\0\0\0\128"] = "\35",
	}

	local binaryPropHandlers = {
		["string"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				result[i] = s_pack("<I4",#val)..val
			end
			return concat(result)
		end,
		["ContentId"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				--if sub(val,1,15) == "rbxgameasset://" then -- This doesn't load anymore
				--val = format("https://assetdelivery.roblox.com/v1/asset?universeId=%d&assetName=%s&skipSigningScripts=1",gameId,urlEncode(httpService,sub(val,16)))
				--end
				result[i] = s_pack("<I4",#val)..val
			end
			return concat(result)
		end,
		["BinaryString"] = function(objs,name,func)
			if not getbspval then return end

			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val = getbspval(objs[i],name) or ""

				result[i] = s_pack("<I4",#val)..val
			end
			return concat(result)
		end,
		["bool"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				result[i] = val and "\1" or "\0"
			end
			return concat(result)
		end,
		["int"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*szObjs)
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local bytes = s_pack(">I4", val < 0 and 2 * -val - 1 or 2 * val)
				for b = 1,4 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end,
		["float"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*szObjs)
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local bytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val)), 1))
				for b = 1,4 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end,
		["double"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				result[i] = s_pack("<d", val)
			end
			return concat(result)
		end,
		["UDim"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(2*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			for i = 1,szObjs do
				local scaleStart = i-1
				local offsetStart = firstArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local offset = val.Offset

				local scaleBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.Scale)), 1))
				local offsetBytes = s_pack(">I4", offset < 0 and 2 * -offset - 1 or 2 * offset)			

				for b = 1,4 do
					result[scaleStart + b + sep*(b-1)] = sub(scaleBytes,b,b)
					result[offsetStart + b + sep*(b-1)] = sub(offsetBytes,b,b)
				end
			end
			return concat(result)
		end,
		["UDim2"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			local secondArrayEnd = 2*4*szObjs
			local thirdArrayEnd = 3*4*szObjs
			for i = 1,szObjs do
				local xScaleStart = i-1
				local yScaleStart = firstArrayEnd + i-1
				local xOffsetStart = secondArrayEnd + i-1
				local yOffsetStart = thirdArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local x,y = val.X,val.Y

				local xOffset = x.Offset
				local yOffset = y.Offset

				local xScaleBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", x.Scale)), 1))
				local xOffsetBytes = s_pack(">I4", xOffset < 0 and 2 * -xOffset - 1 or 2 * xOffset)
				local yScaleBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", y.Scale)), 1))
				local yOffsetBytes = s_pack(">I4", yOffset < 0 and 2 * -yOffset - 1 or 2 * yOffset)

				for b = 1,4 do
					result[xScaleStart + b + sep*(b-1)] = sub(xScaleBytes,b,b)
					result[xOffsetStart + b + sep*(b-1)] = sub(xOffsetBytes,b,b)
					result[yScaleStart + b + sep*(b-1)] = sub(yScaleBytes,b,b)
					result[yOffsetStart + b + sep*(b-1)] = sub(yOffsetBytes,b,b)
				end
			end
			return concat(result)
		end,
		["Ray"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local origin = val.Origin
				local dir = val.Direction
				result[i] = s_pack("<ffffff", origin.X, origin.Y, origin.Z, dir.X, dir.Y, dir.Z)
			end
			return concat(result)
		end,
		["Faces"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local faceInt = (val.Front and 32 or 0) + (val.Bottom and 16 or 0) + (val.Left and 8 or 0) + (val.Back and 4 or 0) + (val.Top and 2 or 0) + (val.Right and 1 or 0)
				result[i] = s_pack("b", faceInt)
			end
			return concat(result)
		end,
		["Axes"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local axisInt = (val.Z and 4 or 0) + (val.Y and 2 or 0) + (val.X and 1 or 0)
				result[i] = s_pack("b", axisInt)
			end
			return concat(result)
		end,
		["BrickColor"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*szObjs)
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local bytes = s_pack(">I4", val.Number)
				for b = 1,4 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end,
		["Color3"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(3*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			local secondArrayEnd = 8*szObjs
			for i = 1,szObjs do
				local rStart = i-1
				local gStart = firstArrayEnd + i-1
				local bStart = secondArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local rBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.R)), 1))
				local gBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.G)), 1))
				local bBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.B)), 1))

				for b = 1,4 do
					result[rStart + b + sep*(b-1)] = sub(rBytes,b,b)
					result[gStart + b + sep*(b-1)] = sub(gBytes,b,b)
					result[bStart + b + sep*(b-1)] = sub(bBytes,b,b)
				end
			end
			return concat(result)
		end,
		["Vector2"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(2*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			for i = 1,szObjs do
				local xStart = i-1
				local yStart = firstArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local xBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.X)), 1))
				local yBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.Y)), 1))

				for b = 1,4 do
					result[xStart + b + sep*(b-1)] = sub(xBytes,b,b)
					result[yStart + b + sep*(b-1)] = sub(yBytes,b,b)
				end
			end
			return concat(result)
		end,
		["Vector3"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(3*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			local secondArrayEnd = 8*szObjs
			for i = 1,szObjs do
				local xStart = i-1
				local yStart = firstArrayEnd + i-1
				local zStart = secondArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local xBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.X)), 1))
				local yBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.Y)), 1))
				local zBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", val.Z)), 1))

				for b = 1,4 do
					result[xStart + b + sep*(b-1)] = sub(xBytes,b,b)
					result[yStart + b + sep*(b-1)] = sub(yBytes,b,b)
					result[zStart + b + sep*(b-1)] = sub(zBytes,b,b)
				end
			end
			return concat(result)
		end,
		["CFrame"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs + 3*4*szObjs)
			local sep = szObjs-1
			local posStart = szObjs
			local firstArrayEnd = posStart + 4*szObjs
			local secondArrayEnd = posStart + 8*szObjs
			for i = 1,szObjs do
				local xStart = posStart + i-1
				local yStart = firstArrayEnd + i-1
				local zStart = secondArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local componentStr = s_pack("<fffffffff",select(4,components(val)))
				result[i] = binaryCFrameMap[componentStr] or "\0"..componentStr

				local pos = val.Position
				local xBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.X)), 1))
				local yBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.Y)), 1))
				local zBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.Z)), 1))

				for b = 1,4 do
					result[xStart + b + sep*(b-1)] = sub(xBytes,b,b)
					result[yStart + b + sep*(b-1)] = sub(yBytes,b,b)
					result[zStart + b + sep*(b-1)] = sub(zBytes,b,b)
				end
			end
			return concat(result)
		end,
		["Enum"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*szObjs)
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local bytes = s_pack(">I4", val.Value)
				for b = 1,4 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end,
		["Vector3int16"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				result[i] = s_pack("<i2i2i2", val.X, val.Y, val.Z)
			end
			return concat(result)
		end,
		["NumberSequence"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local numKeypoints = #val.Keypoints
				result[i] = s_pack("<I4"..s_rep("fff",numKeypoints), numKeypoints, unpack(split(tostring(val)," ")))
			end
			return concat(result)
		end,
		["ColorSequence"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local numKeypoints = #val.Keypoints
				result[i] = s_pack("<I4"..s_rep("fffff",numKeypoints), numKeypoints, unpack(split(tostring(val)," ")))
			end
			return concat(result)
		end,
		["NumberRange"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				result[i] = s_pack("<ff", val.Min, val.Max)
			end
			return concat(result)
		end,
		["Rect"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*4*szObjs)
			local sep = szObjs-1
			local firstArrayEnd = 4*szObjs
			local secondArrayEnd = 2*4*szObjs
			local thirdArrayEnd = 3*4*szObjs
			for i = 1,szObjs do
				local xMinStart = i-1
				local yMinStart = firstArrayEnd + i-1
				local xMaxStart = secondArrayEnd + i-1
				local yMaxStart = thirdArrayEnd + i-1

				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local min = val.Min
				local max = val.Max

				local xMinBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", min.X)), 1))
				local yMinBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", min.Y)), 1))
				local xMaxBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", max.X)), 1))
				local yMaxBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", max.Y)), 1))

				for b = 1,4 do
					result[xMinStart + b + sep*(b-1)] = sub(xMinBytes,b,b)
					result[yMinStart + b + sep*(b-1)] = sub(yMinBytes,b,b)
					result[xMaxStart + b + sep*(b-1)] = sub(xMaxBytes,b,b)
					result[yMaxStart + b + sep*(b-1)] = sub(yMaxBytes,b,b)
				end
			end
			return concat(result)
		end,
		["PhysicalProperties"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				if val then
					result[i] = "\1"..s_pack("<fffff", val.Density, val.Friction, val.Elasticity, val.FrictionWeight, val.ElasticityWeight)
				else
					result[i] = "\0"
				end
			end
			return concat(result)
		end,
		["Color3uint8"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				result[i] = "\1"..s_pack("<bbb", val.R, val.G, val.B)
			end
			return concat(result)
		end,
		["int64"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(8*szObjs)
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local bytes = s_pack(">I8", val < 0 and 2 * -val - 1 or 2 * val)
				for b = 1,8 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end,
		["OptionalCoordinateFrame"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(1 + szObjs + 3*4*szObjs + 1 + szObjs)
			local sep = szObjs-1
			local posStart = szObjs
			local firstArrayEnd = posStart + 4*szObjs
			local secondArrayEnd = posStart + 8*szObjs
			local thirdArrayEnd = posStart + 12*szObjs
			local startOffset = 1

			result[1] = "\16"
			result[startOffset + thirdArrayEnd + 1] = "\2"

			for i = 1,szObjs do
				local xStart = startOffset + posStart + i-1
				local yStart = startOffset + firstArrayEnd + i-1
				local zStart = startOffset + secondArrayEnd + i-1
				local boolPos = startOffset + thirdArrayEnd + i+1

				local val,exists
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				if not val then exists = false val = CFrame.new() else exists = true end

				local componentStr = s_pack("<fffffffff",select(4,components(val)))
				result[startOffset + i] = binaryCFrameMap[componentStr] or "\0"..componentStr

				local pos = val.Position
				local xBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.X)), 1))
				local yBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.Y)), 1))
				local zBytes = s_pack(">I4", lrotate(s_unpack(">I4", s_pack(">f", pos.Z)), 1))

				for b = 1,4 do
					result[xStart + b + sep*(b-1)] = sub(xBytes,b,b)
					result[yStart + b + sep*(b-1)] = sub(yBytes,b,b)
					result[zStart + b + sep*(b-1)] = sub(zBytes,b,b)
				end

				result[boolPos] = exists and "\1" or "\0"
			end
			return concat(result)
		end,
		["Font"] = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end

				local family = s_pack("<I4",#val.Family)..val.Family
				local weight = s_pack("<I2",val.Weight.Value)
				local style = s_pack("<I1",val.Style.Value)
				local cached = "\0\0\0\0"--s_pack("<I4",0)..""

				result[i] = family..weight..style..cached
			end
			return concat(result)
		end,
	}

	binaryPropHandlers.Content = binaryPropHandlers.ContentId

	local specialProps = {
		["Script"] = {
			{Name = "Source", ValueType = {Name = "ProtectedString", Category = "DataType"}, Special = "Decompile"}
		},
		["ModuleScript"] = {
			{Name = "Source", ValueType = {Name = "ProtectedString", Category = "DataType"}, Special = "Decompile"}
		},
		["TerrainRegion"] = { -- TODO: Vector3int16 support for gethiddenprop
			{Name = "ExtentsMin", ValueType = {Name = "Vector3int16", Category = "DataType"}, Special = "Func", Func = function(obj) return workspace.Terrain.MaxExtents.Min end},
			{Name = "ExtentsMax", ValueType = {Name = "Vector3int16", Category = "DataType"}, Special = "Func", Func = function(obj) return workspace.Terrain.MaxExtents.Max end},
		},
		["Model"] = { -- TODO: OptionalCoordinateFrame support for gethiddenprop
			{Name = "WorldPivotData", ValueType = {Name = "OptionalCoordinateFrame", Category = "DataType"}, IndexName = "WorldPivot"},
		},
	}

	--[[
	local specialProps = {
		["Instance"] = {
			{Name = "AttributesSerialize", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "Tags", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
		},
		["TriangleMeshPart"] = {
			{Name = "LODData", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "PhysicalConfigData", ValueType = {Name = "SharedString"}, Special = "SharedString"},
		},
		["PartOperation"] = {
			{Name = "AssetId", ValueType = {Name = "Content"}, Special = "NotScriptable"},
			{Name = "InitialSize", ValueType = {Name = "Vector3"}, Special = "NotScriptable"},
			{Name = "ChildData", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "MeshData", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "PhysicsData", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "ChildData2", ValueType = {Name = "SharedString"}, Special = "SharedString"},
			{Name = "MeshData2", ValueType = {Name = "SharedString"}, Special = "SharedString"},
			{Name = "FormFactor", ValueType = {Name = "FormFactor", Category = "Enum"}, Special = "NotScriptable"},
		},
		["MeshPart"] = {
			{Name = "InitialSize", ValueType = {Name = "Vector3"}, Special = "NotScriptable"},
			{Name = "PhysicsData", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
		},
		["Terrain"] = {
			{Name = "Decoration", ValueType = {Name = "bool"}, Special = "NotScriptable"},
			{Name = "MaterialColors", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "SmoothGrid", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "PhysicsGrid", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
		},
		["TerrainRegion"] = { -- TODO: Vector3int16 support for gethiddenprop
			{Name = "SmoothGrid", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
			{Name = "ExtentsMin", ValueType = {Name = "Vector3int16"}, Special = "Func", Func = function(obj) return workspace.Terrain.MaxExtents.Min end},
			{Name = "ExtentsMax", ValueType = {Name = "Vector3int16"}, Special = "Func", Func = function(obj) return workspace.Terrain.MaxExtents.Max end},
		},
		["BinaryStringValue"] = {
			{Name = "Value", ValueType = {Name = "BinaryString"}, Special = "BinaryString"},
		},
		["Workspace"] = {
			{Name = "PGSPhysicsSolverEnabled", ValueType = {Name = "bool"}, Special = "Func", Func = function(obj) return obj:PGSIsEnabled() end},
			{Name = "CollisionGroups", ValueType = {Name = "string"}, Special = "Func", Func = function(obj)
				local groupTable = {}
				for i,v in pairs(game:GetService("PhysicsService"):GetCollisionGroups()) do
					groupTable[i] = v.name.."^"..v.id.."^"..v.mask
				end
				return table.concat(groupTable,"\\")
			end}
		},
		["Humanoid"] = {
			{Name = "Health_XML", ValueType = {Name = "float"}, IndexName = "Health"},
		},
		["Sound"] = {
			{Name = "xmlRead_MaxDistance_3", ValueType = {Name = "float"}, IndexName = "MaxDistance"},
		},
		["WeldConstraint"] = {
			{Name = "CFrame0", ValueType = {Name = "CFrame"}, Special = "NotScriptable"},
			{Name = "CFrame1", ValueType = {Name = "CFrame"}, Special = "NotScriptable"},
			{Name = "Part0Internal", ValueType = {Name = "Instance"}, IndexName = "Part0"},
			{Name = "Part1Internal", ValueType = {Name = "Instance"}, IndexName = "Part1"}
		},
		["Lighting"] = {
			{Name = "Technology", ValueType = {Category = "Enum"}, Special = "NotScriptable"}
		},
		["LocalizationTable"] = {
			{Name = "Contents", ValueType = {Name = "string"}, Special = "NotScriptable"}
		},
		["Script"] = {
			{Name = "Source", ValueType = {Name = "ProtectedString"}, Special = "Decompile"}
		},
		["ModuleScript"] = {
			{Name = "Source", ValueType = {Name = "ProtectedString"}, Special = "Decompile"}
		},
		["PackageLink"] = {
			{Name = "PackageIdSerialize", ValueType = {Name = "Content"}, IndexName = "PackageId"},
			{Name = "VersionIdSerialize", ValueType = {Name = "int64"}, IndexName = "VersionNumber"}
		}
	}
	]]

	local readMeStart = [==[--[[
	Thank you for using Dex SaveInstance.
	You are recommended to save the game (if you used saveplace) right away to take advantage of the binary format (if you didn't save in binary).
	If your player cannot spawn into the game, please move the scripts in StarterPlayer elsewhere. (This is done by default)
	If the chat system does not work, please use the explorer and delete everything inside the Chat service. (Or run game:GetService("Chat"):ClearAllChildren())
	
	If union and meshpart collisions don't work, first run this script in the Studio command bar:
	local list = {}
	local coreGui = game:GetService("CoreGui")

	for i,v in pairs(game:GetDescendants()) do
		local s,e = pcall(function() return v:IsA("UnionOperation") or v:IsA("MeshPart") end)
		if s and e and not v:IsDescendantOf(coreGui) then
			list[#list+1] = v
		end
	end

	game.Selection:Set(list)
	
	After running it, go to the Properties window and change CollisionFidelity from "Box" to "Default".

	
	This file was generated with the following settings:
	
]==]

	local function getSaveProps(obj,class)
		local result = {}
		local count = 1

		local curClass = API.Classes[class]
		while curClass do
			local curClassName = curClass.Name
			local cacheProps = saveProps[curClassName]
			if cacheProps then
				table.move(cacheProps,1,#cacheProps,#result+1,result)
				break
			end

			local props = curClass.Properties
			for i = 1,#props do
				local prop = props[i]
				local propName = prop.Name
				--if (prop.Serialization.CanSave and not prop.Tags.NotScriptable) or (propBypass[curClassName] and propBypass[curClassName][propName]) then
				if prop.Serialization.CanSave or (propBypass[curClassName] and propBypass[curClassName][propName]) then
					if not propFilter[curClassName] or not propFilter[curClassName][propName] then
						-- Check for existence in current engine version
						if prop.Tags and prop.Tags.NotScriptable then
							local s,ret1,ret2 = pcall(getnspval,obj,propName)
							if s and type(ret2) ~= "string" then
								result[count] = prop
								count = count + 1
							end
						else
							local s,e = pcall(function() return obj[propName] end)
							if s then
								result[count] = prop
								count = count + 1
							end
						end
					end
				end
			end

			-- Special props may also contain alternate defs for filtered props
			local specialProps = specialProps[curClassName]
			if specialProps then
				table.move(specialProps,1,#specialProps,#result+1,result)
				count = #result+1
			end

			curClass = curClass.Superclass
		end

		table.sort(result,function(a,b) return a.Name < b.Name end)
		return result
	end

	local function getTestInst(class)
		local s,inst = pcall(Instance.new,class)
		if not s then return {} end

		local defaultProps = {}

		local props = saveProps[class]
		for i = 1,#props do
			local prop = props[i]
			if not prop.Special and not (prop.Tags and prop.Tags.NotScriptable) then
				local propName = prop.IndexName or prop.Name
				defaultProps[propName] = inst[propName]
			end
		end

		return defaultProps
	end

	local function doDecompile(scr,saveSettings)
		if injectedDecompiler then
			local ok, source, err = pcall(injectedDecompiler, scr, saveSettings)
			if not ok then
				return nil, tostring(source)
			end
			return source, err
		end

		if type(decompile) ~= "function" then
			return nil, "no decompiler was injected and executor decompile() is unavailable"
		end

		local thread = coroutine.running()
		local finished = false

		if elysianexecute then
			local s,e = decompile(scr,function(src,err)
				if not finished then
					finished = true
					coroutine.resume(thread,src,err)
				end
			end,saveSettings.DecompileTimeout)

			if not s then return nil, e end
		else
			return decompile(scr,nil,saveSettings.DecompileTimeout)
		end

		task.spawn(function()
			task.wait(saveSettings.DecompileTimeout + 1)
			if not finished then
				finished = true
				coroutine.resume(thread, nil, "decompile failed: decompiler timed out")
			end
		end)

		return coroutine.yield()
	end

	local function createStatusText()
		local statusText
		if syn or elysianexecute then
			statusText = Drawing.new("Text")
			statusText.Color = Color3.new(1,1,1)
			statusText.Outline = true
			statusText.OutlineColor = Color3.new(0,0,0)
			statusText[syn and "Size" or "FontSize"] = 50
			if syn then statusText.Visible = true end
		else
			return nil
		end

		local function updateStatus(text)
			local viewport = workspace.CurrentCamera.ViewportSize
			statusText.Text = text or ""
			statusText.Position = Vector2.new(viewport.X / 2 - statusText.TextBounds.X / 2, 50)
		end

		local function removeStatus()
			statusText:Remove()
		end

		return {Update = updateStatus, Remove = removeStatus}
	end

	local function predecompile(root,statusText,saveSettings)
		if not saveSettings.Decompile then return {} end

		local scripts,sources,checked = {},{},{}
		local ignoredServices
		local scriptCount,totalScripts = 1,0

		if root == game and saveSettings.DecompileIgnore then
			ignoredServices = {}
			for i,v in pairs(saveSettings.DecompileIgnore) do
				ignoredServices[i] = game:GetService(v)
			end
		end

		local isTable = type(root) == "table"
		local objs = isTable and root or {root}
		local maxThreads = saveSettings.MaxThreads or 3
		local isDescendantOf = game.IsDescendantOf

		if saveSettings.NilInstances and root == game and getnilinstances then
			local nilInsts = getnilinstances()
			table.move(nilInsts,1,#nilInsts,#objs+1,objs)
		end

		for i = 1,#objs do
			local nextRoot = objs[i]
			local descs = nextRoot:GetDescendants()
			descs[0] = nextRoot
			for i = 0,#descs do
				local obj = descs[i]
				if (isa(obj,"LocalScript") or isa(obj,"ModuleScript")) and not checked[obj] then
					local ignored = false
					if ignoredServices then
						for i = 1,#ignoredServices do
							if isDescendantOf(obj,ignoredServices[i]) then
								ignored = true
								break
							end
						end
					end

					if not ignored then
						scripts[scriptCount] = obj
						scriptCount = scriptCount + 1
					end

					checked[obj] = true
				end
			end
		end
		totalScripts = scriptCount - 1

		local left = totalScripts
		for i = 1,maxThreads do
			task.spawn(function()
				while #scripts > 0 do
					local nextScript = table.remove(scripts)
					local source, err = doDecompile(nextScript,saveSettings)

					if source then
						sources[nextScript] = source
					else
						sources[nextScript] = "-- This script could not be decompiled because:\n-- "..(err or "N/A")
					end

					left = left - 1
					if statusText then
						statusText.Update("Decompiling scripts... (" .. (totalScripts - left) .. "/" .. totalScripts .. ")")
					end
				end
			end)
		end

		while left > 0 do task.wait() end

		return sources
	end

	local function serializeBinary(root,filename,saveSettings)
		local mainBuf = {}

		local header = {"\60\114\111\98\108\111\120\33\137\255\13\10\26\10\0\0","","","\0\0\0\0\0\0\0\0"}
		local metaBuf = {"\77\69\84\65\36\0\0\0\34\0\0\0\0\0\0\0\240\19\1\0\0\0\18\0\0\0\69\120\112\108\105\99\105\116\65\117\116\111\74\111\105\110\116\115\4\0\0\0\116\114\117\101"}
		local sstrBuf = {}
		local instBuf,instBufCount = {},1
		local propBuf,propBufCount = {},1
		local prntBuf = {}
		local endBuf = {"\69\78\68\0\0\0\0\0\9\0\0\0\0\0\0\0\60\47\114\111\98\108\111\120\62"}

		local instTypeCount = 0
		local instCount = 0
		local refCount = 0
		local sharedStringCount = 0

		local isGame = root == game
		local isTable = type(root) == "table"

		local startB = tick()
		local classList = {}
		local hashs = {}
		local sharedStrings = {}
		local filter = {}
		local refs = {}
		local parents = {}
		local orderedInstList = {}
		local nilBlacklist = {[game] = true}
		local folderClasses = {["Player"] = true, ["PlayerScripts"] = true, ["PlayerGui"] = true, ["ScriptDebugger"] = true, ["Breakpoints"] = true, ["DebuggerWatch"] = true}
		local savingDefaultProps = not saveSettings.IgnoreDefaultProps
		local decompileEnabled = saveSettings.Decompile

		if isTable and not root[1] then error("Empty Table") end

		-- Set up filter
		if isGame then
			for i,v in pairs(service.Players:GetPlayers()) do
				if not saveSettings.SavePlayers then
					filter[v] = true
				end

				if saveSettings.RemovePlayerCharacters and v.Character then
					filter[v.Character] = true
				end
			end
		end

		if saveSettings.IsolateStarterPlayer then
			folderClasses["StarterPlayer"] = true
			folderClasses["StarterCharacterScripts"] = true
			folderClasses["StarterPlayerScripts"] = true
		end

		if not filename then
			filename = isGame and "Place_"..game.PlaceId or "Place_"..game.PlaceId.."_Inst_"..(isTable and root[1] or root):GetDebugId()
		end
		if isGame then
			filename = filename:match("%.rbxlx?$") and filename or filename..".rbxl"
		else	
			filename = filename:match("%.rbxmx?$") and filename or filename..".rbxm"
		end

		if not saveSettings.Clipboard and not saveSettings.Callback then
			env.writefile(filename,"")
		end

		local statusText = saveSettings.ShowStatus and createStatusText()
		local sources = predecompile(root,statusText,saveSettings)

		-- Count instances and instance types
		local function recur(obj)
			if filter[obj] then return end

			local class = oldIndex and oldIndex(obj,"ClassName") or obj.ClassName
			if folderClasses[class] then
				class = "Folder"
				if not saveProps["Folder"] then saveProps["Folder"] = getSaveProps(Instance.new("Folder"),"Folder") end
			end

			if not saveProps[class] then saveProps[class] = getSaveProps(obj,class) end

			if not testInsts[class] then testInsts[class] = (not savingDefaultProps and getTestInst(class) or {}) end

			local ch = getChildren(obj)
			local szCh = #ch
			if szCh > 0 then
				for i = 1,szCh do
					local chObj = ch[i]
					parents[chObj] = obj
					recur(chObj)
				end
			end

			if not refs[obj] then
				instCount = instCount + 1
				orderedInstList[instCount] = obj

				local cList = classList[class]
				if not cList then
					cList = {}
					classList[class] = cList
					instTypeCount = instTypeCount + 1
				end
				cList[#cList+1] = obj

				refs[obj] = refCount
				refCount = refCount + 1
			end
		end

		if isGame then
			local gameCh = getChildren(root)
			for i = 1,#gameCh do
				local obj = gameCh[i]
				if not serviceBlacklist[obj.ClassName] then
					recur(obj)
				end
			end

			local message = readMeStart

			for i, v in next, saveSettings do
				if type(v) == "table" then -- assume array
					local strings = {}
					for j, k in next, v do
						strings[#strings+1] = type(k) == "string" and ("\"" .. tostring(k) .. "\"") or tostring(v)
					end
					message = message .. "\t" .. tostring(i) .. " = { " .. table.concat(strings, ", ") .. " }\n"
				elseif i ~= "_Recurse" then
					message = message .. "\t" .. tostring(i) .. " = " .. tostring(v) .. "\n"
				end
			end

			message = message .. "]]"

			local readmeScript = Instance.new("Script")
			readmeScript.Name = "README"
			nilBlacklist[readmeScript] = true
			sources[readmeScript] = message
			recur(readmeScript)
		elseif isTable then
			for i = 1,#root do
				recur(root[i])
			end
		else
			recur(root)
		end

		-- Nil Instances
		if saveSettings.NilInstances and root == game and getnilinstances then
			local nilFolder = Instance.new("Folder")
			nilFolder.Name = "Nil Instances"
			nilBlacklist[nilFolder] = true
			recur(nilFolder)

			local classes = API.Classes
			local nilInsts = getnilinstances()
			for i = 1,#nilInsts do
				local obj = nilInsts[i]
				local class = oldIndex and oldIndex(obj,"ClassName") or obj.ClassName
				if classes[class] and not classes[class].Tags.Service and not classes[class].Tags.NotCreatable and not nilBlacklist[obj] then
					local parentClass = nilClassParents[class]
					if parentClass then
						local parentObj = Instance.new(parentClass)
						parentObj.Name = class.." Class"
						recur(parentObj)
						parents[parentObj] = nilFolder

						recur(obj)
						parents[obj] = parentObj
					else
						local isNilSafe = nilSafe[class]
						if isNilSafe == nil then
							isNilSafe = true
							local folder = Instance.new("Folder")
							local s,inst = pcall(Instance.new,class)
							if s and not pcall(function() inst.Parent = folder end) then
								isNilSafe = false
							end
							nilSafe[class] = isNilSafe
						end
						if isNilSafe then
							recur(obj)
							parents[obj] = nilFolder
						end
					end
				end
			end
		end

		-- Special Handlers
		local refPropHandler = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(4*szObjs)
			local sep = szObjs-1

			local lastRef
			for i = 1,szObjs do
				local start = i-1
				local val
				if func then val = func(objs[i],name) elseif oldIndex then val = oldIndex(objs[i],name) else val = objs[i][name] end
				local ref = refs[val] or -1
				local accRef

				-- Accumulation
				accRef = lastRef and (ref - lastRef) or ref
				lastRef = ref

				local transformed = (accRef < 0 and 2 * -accRef - 1 or 2 * accRef)
				local bytes = s_pack(">I4",transformed)

				for b = 1,4 do
					result[start + b + sep*(b-1)] = sub(bytes,b,b)
				end
			end
			return concat(result)
		end

		local sharedStringHandler = function(objs,name,func)
			if not gethiddenprop then return end

			if sharedStringCount == 0 then
				sharedStringCount = sharedStringCount + 1
				sharedStrings[1] = {"NullSharedString",""}
			end

			local szObjs = #objs
			local result = tableCreate(4*szObjs,"\0")
			local sep = szObjs-1
			for i = 1,szObjs do
				local start = i-1
				local content = gethiddenprop(objs[i],name)
				if content and #content > 0 then
					local hash = content
					local index = hashs[hash]
					if not index then
						index = sharedStringCount
						hashs[hash] = index
						sharedStringCount = sharedStringCount + 1
						sharedStrings[sharedStringCount] = {s_pack(">I16",sharedStringCount),content}
					end

					local bytes = s_pack(">I4", index)
					for b = 1,4 do
						result[start + b + sep*(b-1)] = sub(bytes,b,b)
					end
				end
			end
			return concat(result)
		end

		local protectedStringHandler = function(objs,name,func)
			local szObjs = #objs
			local result = tableCreate(szObjs)
			for i = 1,szObjs do
				local val
				if sources[objs[i]] then
					val = sources[objs[i]]
				elseif not decompileEnabled then
					val = "-- Decompiling is disabled"
				else
					val = "-- Script failed to decompile or ignored"
				end

				result[i] = s_pack("<I4",#val)..val
			end
			return concat(result)
		end

		local typeId = 0
		for class,objs in next,classList do
			-- Make INST chunk
			local instHeader = {"INST","\0\0\0\0","","\0\0\0\0"}
			local instChunkData = tableCreate(4 + 4*#objs,"")
			local typeIdBytes = s_pack("<I4",typeId)
			local isService = API.Classes[class] and API.Classes[class].Tags.Service
			instChunkData[1] = typeIdBytes
			instChunkData[2] = s_pack("<I4",#class)..class
			instChunkData[3] = isService and "\1" or "\0"
			instChunkData[4] = s_pack("<I4",#objs)

			local lastRef
			local sep = #objs-1
			for i = 1,#objs do
				local start = 4 + (i-1)
				local obj = objs[i]
				local ref = refs[obj]
				local accRef

				-- Accumulation
				accRef = lastRef and (ref - lastRef) or ref
				lastRef = ref

				local transformed = (accRef < 0 and 2 * -accRef - 1 or 2 * accRef)
				local bytes = s_pack(">I4",transformed)

				for b = 1,4 do
					local chunkIndex = start + b + sep*(b-1)
					instChunkData[chunkIndex] = sub(bytes,b,b)
				end
			end

			if isService then
				instChunkData[#instChunkData+1] = s_rep("\1",#objs)
			end

			instChunkData = concat(instChunkData)
			instHeader[3] = s_pack("<I4",#instChunkData)

			if lz4compress then
				instChunkData = lz4compress(instChunkData)
				instHeader[2] = s_pack("<I4",#instChunkData)
			end

			instBuf[instBufCount] = concat(instHeader)
			instBuf[instBufCount+1] = instChunkData
			instBufCount = instBufCount + 2


			-- Make PROP chunk
			local props = saveProps[class]
			for propInd = 1,#props do
				local prop = props[propInd]
				local propName = prop.Name
				local indexName = prop.IndexName or propName
				local typeData = prop.ValueType
				local propTypeCategory = typeData.Category
				local propType = typeData.Name

				local propHeader = {"PROP","\0\0\0\0","","\0\0\0\0"}
				local propChunkData = {typeIdBytes, s_pack("<I4",#propName)..propName, nil, ""}

				local handler
				if propTypeCategory == "Primitive" or propTypeCategory == "DataType" then
					handler = binaryPropHandlers[propType]
					propChunkData[3] = binaryDataTypes[propType]

					if not handler then
						if propType == "SharedString" then
							handler = sharedStringHandler
						elseif propType == "ProtectedString" then
							handler = protectedStringHandler
							propChunkData[3] = binaryDataTypes.string
						end
					end
				elseif propTypeCategory == "Enum" then
					handler = binaryPropHandlers.Enum
					propChunkData[3] = binaryDataTypes.Enum
				else -- Assume Class
					handler = refPropHandler
					propChunkData[3] = binaryDataTypes.Referent
				end

				if handler then
					local func
					local special = prop.Special

					if prop.Tags and prop.Tags.NotScriptable then
						if getnspval then
							func = getnspval
						else
							continue
						end
						--local s,ret1,ret2 = pcall(getnspval,objs[1],indexName)
						--if not s or type(ret2) == "string" then -- Some hidden properties may not exist
						--	continue
						--end
					end

					if special then
						if special == "NotScriptable" then
							if getnspval then
								func = getnspval

								--local s,ret1,ret2 = pcall(getnspval,objs[1],indexName)
								--if not s or type(ret2) == "string" then -- Some hidden properties may not exist
								--	continue
								--end
							else
								continue
							end
						elseif special == "Func" then
							func = prop.Func
						end
					end

					local propData = handler(objs,indexName,func)
					if not propData then continue end
					propChunkData[4] = propData

					propChunkData = concat(propChunkData)
					propHeader[3] = s_pack("<I4",#propChunkData)

					if lz4compress then
						propChunkData = lz4compress(propChunkData)
						propHeader[2] = s_pack("<I4",#propChunkData)
					end

					propBuf[propBufCount] = concat(propHeader)
					propBuf[propBufCount+1] = propChunkData
					propBufCount = propBufCount + 2
				end
			end

			typeId = typeId + 1
		end


		-- Make SSTR chunk
		if sharedStringCount > 0 then
			local sstrHeader = {"SSTR","\0\0\0\0","","\0\0\0\0"}
			local sstrChunkData = {"\0\0\0\0",s_pack("<I4",sharedStringCount)}
			local count = 3

			for i = 1,#sharedStrings do
				local data = sharedStrings[i]
				local hash,content = data[1],data[2]
				sstrChunkData[count] = hash..s_pack("<I4",#content)..content
				count = count + 1
			end

			sstrChunkData = concat(sstrChunkData)
			sstrHeader[3] = s_pack("<I4",#sstrChunkData)

			if lz4compress then
				sstrChunkData = lz4compress(sstrChunkData)
				sstrHeader[2] = s_pack("<I4",#sstrChunkData)
			end

			sstrBuf[1] = concat(sstrHeader)
			sstrBuf[2] = sstrChunkData
		end


		-- Make PRNT chunk
		local function makePRNT()
			local prntHeader = {"PRNT","\0\0\0\0","","\0\0\0\0"}
			local prntChunkData = tableCreate(2 + 2*4*instCount)
			prntChunkData[1] = "\0"
			prntChunkData[2] = s_pack("<I4",instCount)

			local lastObjRef,lastParRef
			local sep = instCount-1
			local prntRefCount = 1
			local lastObjIndex = 2 + 4*instCount
			for i = 1,instCount do
				local obj = orderedInstList[i]
				local ref = refs[obj]

				local objStart = 2 + (prntRefCount-1)
				local parStart = lastObjIndex + (prntRefCount-1)

				local par = parents[obj]
				local parRef = refs[par] or -1

				local accObjRef
				local accParRef

				-- Accumulation
				accObjRef = lastObjRef and (ref - lastObjRef) or ref
				lastObjRef = ref

				accParRef = lastParRef and (parRef - lastParRef) or parRef
				lastParRef = parRef

				-- Interleave obj and parent bytes
				local objTransformed = (accObjRef < 0 and 2 * -accObjRef - 1 or 2 * accObjRef)
				local objBytes = s_pack(">I4",objTransformed)
				local parTransformed = (accParRef < 0 and 2 * -accParRef - 1 or 2 * accParRef)
				local parBytes = s_pack(">I4",parTransformed)

				for b = 1,4 do
					local objChunkIndex = objStart + b + sep*(b-1)
					local parChunkIndex = parStart + b + sep*(b-1)
					prntChunkData[objChunkIndex] = sub(objBytes,b,b)
					prntChunkData[parChunkIndex] = sub(parBytes,b,b)
				end	

				prntRefCount = prntRefCount + 1
			end

			prntChunkData = concat(prntChunkData)
			prntHeader[3] = s_pack("<I4",#prntChunkData)

			if lz4compress then
				prntChunkData = lz4compress(prntChunkData)
				prntHeader[2] = s_pack("<I4",#prntChunkData)
			end

			prntBuf[1] = concat(prntHeader)
			prntBuf[2] = prntChunkData
		end
		makePRNT()


		-- Wrap up
		header[2] = s_pack("<i4",instTypeCount)
		header[3] = s_pack("<i4",instCount)

		if not saveSettings.Clipboard and not saveSettings.Callback then
			env.appendfile(filename,concat(header),true)
			env.appendfile(filename,concat(metaBuf),true)
			env.appendfile(filename,concat(sstrBuf),true)
			env.appendfile(filename,concat(instBuf),true)
			env.appendfile(filename,concat(propBuf),true)
			env.appendfile(filename,concat(prntBuf),true)
			env.appendfile(filename,concat(endBuf),true)

			if statusText then
				statusText.Update("Saved to the file "..filename.." in "..(tick()-startB).." secs")
				task.delay(5,statusText.Remove)
			end
		else
			local totalData = {concat(header), concat(metaBuf), concat(sstrBuf), concat(instBuf), concat(propBuf), concat(prntBuf), concat(endBuf)}
			totalData = concat(totalData)

			if saveSettings.Clipboard then
				if setrbxclipboard then
					setrbxclipboard(totalData)
				end
			elseif saveSettings.Callback and type(saveSettings.Callback) == "function" then
				task.spawn(saveSettings.Callback,totalData)
			end
		end
	end

	local function serializeXML(root,filename,saveSettings)
		local isGame = root == game
		local isTable = type(root) == "table"
		if isTable and not root[1] then error("Empty Table") end

		if not filename then
			filename = isGame and "Place_"..game.PlaceId or "Place_"..game.PlaceId.."_Inst_"..(isTable and root[1] or root):GetDebugId()
		end
		if isGame then
			filename = filename:match("%.rbxlx?$") and filename or filename..".rbxlx"
		else	
			filename = filename:match("%.rbxmx?$") and filename or filename..".rbxmx"
		end
		env.writefile(filename,"")

		local startB = tick()
		local folderClasses = {["Player"] = true, ["PlayerScripts"] = true, ["PlayerGui"] = true, ["ScriptDebugger"] = true, ["Breakpoints"] = true, ["DebuggerWatch"] = true}
		local insts = {}
		local refs = {}
		local refCount = 1
		local depths = {}
		local filter = {}
		local hashs = {}
		local sharedStrings = {}
		local savingDefaultProps = not saveSettings.IgnoreDefaultProps
		local decompileEnabled = saveSettings.Decompile
		local statusText = saveSettings.ShowStatus and createStatusText()
		local sources = predecompile(root,statusText,saveSettings)

		-- Set up filter
		if isGame then
			for i,v in pairs(service.Players:GetPlayers()) do
				if not saveSettings.SavePlayers then
					filter[v] = true
				end

				if saveSettings.RemovePlayerCharacters and v.Character then
					filter[v.Character] = true
				end
			end
		end

		if saveSettings.IsolateStarterPlayer then
			folderClasses["StarterPlayer"] = true
			folderClasses["StarterCharacterScripts"] = true
			folderClasses["StarterPlayerScripts"] = true
		end

		local buffer = {'<roblox xmlns:xmime="http://www.w3.org/2005/05/xmlmime" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:noNamespaceSchemaLocation="http://www.roblox.com/roblox.xsd" version="4">\n<Meta name="ExplicitAutoJoints">true</Meta>\n<External>null</External>\n<External>nil</External>'}
		local bufferCount = 2

		local function recur(obj)
			if filter[obj] then return end

			local class = oldIndex and oldIndex(obj,"ClassName") or obj.ClassName
			if folderClasses[class] then
				class = "Folder"
				if not saveProps["Folder"] then saveProps["Folder"] = getSaveProps(Instance.new("Folder"),"Folder") end
			end

			local ref = refs[obj]
			if not ref then ref = refCount refs[obj] = ref refCount = refCount + 1 end

			local props = saveProps[class]
			if not props then props = getSaveProps(obj,class) saveProps[class] = props end

			local testInst = testInsts[class]
			if not testInst then testInst = (not savingDefaultProps and getTestInst(class) or {}) testInsts[class] = testInst end

			buffer[bufferCount] = format('\n<Item class="%s" referent="RBX%d">\n<Properties>',class,ref)
			bufferCount = bufferCount + 1

			for i = 1,#props do
				local prop = props[i]
				local propName = prop.Name
				local indexName = prop.IndexName or propName
				local propVal

				local special = prop.Special
				if special then
					if special == "NotScriptable" then
						propVal = getnspval and getnspval(obj,indexName)
					elseif special == "BinaryString" then
						propVal = getbspval and getbspval(obj,indexName,true)
					elseif special == "SharedString" and gethiddenprop and hashmd5 then
						local content = gethiddenprop(obj,indexName)
						if content and #content > 0 then
							local hash = hashs[content]
							if not hash then
								local rawHash = hashmd5(content)
								local newHash = ""
								for i = 1,#rawHash,2 do
									newHash = newHash..string.char(tonumber(rawHash:sub(i,i+1),16))
								end
								hash = encodeBase64(newHash)
								hashs[content] = hash
							end

							if not sharedStrings[hash] then
								sharedStrings[hash] = encodeBase64(content)
							end
							propVal = hash
						end
					elseif special == "Func" then
						propVal = prop.Func(obj)
					elseif special == "Decompile" then
						if sources[obj] then
							propVal = sources[obj]
						elseif not decompileEnabled then
							propVal = "-- Decompiling is disabled"
						else
							propVal = "-- Script failed to decompile or ignored"
						end
					end
				else
					if oldIndex then propVal = oldIndex(obj,indexName) else propVal = obj[indexName] end
				end

				if testInst[indexName] ~= propVal or (savingDefaultProps and propVal ~= nil) then
					local typeData = prop.ValueType
					local propType = typeData.Name

					local convertFunc = valueConverters[propType]
					if convertFunc then
						buffer[bufferCount] = convertFunc(propName,propVal)
					elseif typeData.Category == "Enum" then
						buffer[bufferCount] = format('\n<token name="%s">%d</token>',propName,propVal.Value)
					elseif classes[propType] and propVal then
						local ref = refs[propVal]
						if not ref then ref = refCount refs[propVal] = ref refCount = refCount + 1 end
						buffer[bufferCount] = format('\n<Ref name="%s">RBX%d</Ref>',propName,ref)
					else
						buffer[bufferCount] = ""
					end
					bufferCount = bufferCount + 1
				end
			end

			buffer[bufferCount] = '\n</Properties>'
			bufferCount = bufferCount + 1

			if bufferCount > 10000 then
				env.appendfile(filename,table.concat(buffer))
				table.clear(buffer)
				bufferCount = 1
			end

			local ch = getChildren(obj)
			local szCh = #ch
			if szCh > 0 then
				for i = 1,szCh do
					recur(ch[i])
				end
			end

			buffer[bufferCount] = '\n</Item>'
			bufferCount = bufferCount + 1
		end

		if isGame then
			local gameCh = getChildren(root)
			for i = 1,#gameCh do
				local obj = gameCh[i]
				if not serviceBlacklist[obj.ClassName] then
					recur(obj)
				end
			end

			local message = readMeStart

			for i, v in next, saveSettings do
				if type(v) == "table" then -- assume array
					local strings = {}
					for j, k in next, v do
						strings[#strings+1] = type(k) == "string" and ("\"" .. tostring(k) .. "\"") or tostring(v)
					end
					message = message .. "\t" .. tostring(i) .. " = { " .. table.concat(strings, ", ") .. " }\n"
				elseif i ~= "_Recurse" then
					message = message .. "\t" .. tostring(i) .. " = " .. tostring(v) .. "\n"
				end

			end

			message = message .. "]]"

			buffer[bufferCount] = [==[

<Item class="Script" referent="RBX999999999">
<Properties>
<string name="Name">README</string>
<ProtectedString name="Source">]==]..gsub(message, xmlReplacePattern, xmlReplace)..[==[</ProtectedString>
</Properties>
</Item>]==]
			bufferCount = bufferCount + 1
		elseif isTable then
			for i = 1,#root do
				recur(root[i])
			end
		else
			recur(root)
		end

		-- Nil Instances
		if saveSettings.NilInstances and root == game and getnilinstances then
			local folderRef = refCount
			refCount = refCount + 1
			buffer[bufferCount] = '\n<Item class="Folder" referent="RBX'..folderRef..'">\n<Properties>\n<string name="Name">Nil Instances</string>\n</Properties>'
			bufferCount = bufferCount + 1

			local classes = API.Classes
			local nilInsts = getnilinstances()
			for i = 1,#nilInsts do
				local obj = nilInsts[i]
				local class = oldIndex and oldIndex(obj,"ClassName") or obj.ClassName
				if classes[class] and not classes[class].Tags.Service and not classes[class].Tags.NotCreatable and obj ~= game then
					local parentClass = nilClassParents[class]
					if parentClass then
						local parentRef = refCount
						refCount = refCount + 1
						buffer[bufferCount] = format('\n<Item class="%s" referent="RBX%d">\n<Properties>\n<string name="Name">%s Class</string>\n</Properties>',parentClass,parentRef,class)
						bufferCount = bufferCount + 1
						recur(obj)
						buffer[bufferCount] = "\n</Item>"
						bufferCount = bufferCount + 1
					else
						local isNilSafe = nilSafe[class]
						if isNilSafe == nil then
							isNilSafe = true
							local folder = Instance.new("Folder")
							local s,inst = pcall(Instance.new,class)
							if s and not pcall(function() inst.Parent = folder end) then
								isNilSafe = false
							end
							nilSafe[class] = isNilSafe
						end
						if isNilSafe then recur(obj) end
					end
				end
			end
			buffer[bufferCount] = "\n</Item>"
			bufferCount = bufferCount + 1
		end

		-- SharedStrings
		buffer[bufferCount] = "\n<SharedStrings>"
		bufferCount = bufferCount + 1
		for hash,content in next,sharedStrings do
			buffer[bufferCount] = '\n<SharedString md5="'..hash..'">'..content..'</SharedString>'
			bufferCount = bufferCount + 1
		end

		buffer[bufferCount] = "\n</SharedStrings>\n</roblox>"
		env.appendfile(filename,table.concat(buffer))
		table.clear(buffer)
		table.clear(hashs)
		table.clear(sharedStrings)

		if statusText then
			statusText.Update("Saved to the file "..filename.." in "..(tick()-startB).." secs")
			task.delay(5,statusText.Remove)
		end
	end

	Serializer.SaveInstance = function(root,filename,opts)
		if not gameId then gameId = game.GameId end
		local saveSettings = {}
		for set,val in pairs(Settings.Serializer) do
			if opts and opts[set] ~= nil then
				saveSettings[set] = opts[set]
			else
				saveSettings[set] = val
			end
		end
		if saveSettings.DecompileMode and saveSettings.DecompileMode > 0 then saveSettings.Decompile = true end

		if saveSettings.Binary then
			serializeBinary(root,filename,saveSettings)
		else
			serializeXML(root,filename,saveSettings)
		end
	end

	Serializer.Init = function(oldInd)
		oldIndex = oldInd

		gethiddenprop = env.gethiddenprop or env.getnspval
		getnspval = gethiddenprop
		getbspval = env.getbspval
		getnilinstances = env.getnilinstances
		getpcd = env.getpcd
		encodeBase64 = env.encodeBase64
		lz4compress = env.lz4compress
		classes = API.Classes
		hashmd5 = env.hashmd5

		if not getbspval and gethiddenprop and encodeBase64 then
			getbspval = function(obj,prop,enc)
				local binary = gethiddenprop(obj,prop) or ""
				if #binary == 0 then return nil end
				return enc and encodeBase64(binary) or binary
			end
		end
	end

	return Serializer
end)()

Main = (function()
	local Main = {}

	Main.FetchAPI = function()
		-- You should see if you can use ReflectionService here

		--local robloxVer = game:HttpGet("http://setup.roblox.com/versionQTStudio")
		local rawAPI
		
		if game:GetService("RunService"):IsStudio() then
			rawAPI = require(game.ReplicatedStorage.FullAPI)
		else
			rawAPI = game:HttpGet("https://raw.githubusercontent.com/MaximumADHD/Roblox-Client-Tracker/refs/heads/roblox/Full-API-Dump.json")
		end
		
		local api = service.HttpService:JSONDecode(rawAPI)
		local classes,enums = {},{}

		for _,class in pairs(api.Classes) do
			classes[class.Name] = {
				Name = class.Name,
				Superclass = nil,
				Properties = {},
				Functions = {},
				Events = {},
				Callbacks = {},
				Tags = {},
			}
		end

		for _,class in pairs(api.Classes) do
			local newClass = classes[class.Name]
			newClass.Superclass = classes[class.Superclass]

			if class.Tags then
				for _,tag in pairs(class.Tags) do
					newClass.Tags[tag] = true
				end
			end

			for _,member in pairs(class.Members) do
				local newMember = {
					Name = member.Name,
					Class = class.Name,
					Tags = {},
				}

				if member.Tags then
					for _,tag in pairs(member.Tags) do
						newMember.Tags[tag] = true
					end
				end

				local memberType = member.MemberType
				if memberType == "Property" then
					newMember.ValueType = member.ValueType
					newMember.Category = member.Category
					newMember.Serialization = member.Serialization
					table.insert(newClass.Properties,newMember)
				elseif memberType == "Function" then
					newMember.Parameters = {}
					newMember.ReturnType = member.ReturnType.Name
					for _,param in pairs(member.Parameters) do
						table.insert(newMember.Parameters,{Name = param.Name, Type = param.Type.Name})
					end
					table.insert(newClass.Functions,newMember)
				elseif memberType == "Event" then
					newMember.Parameters = {}
					for _,param in pairs(member.Parameters) do
						table.insert(newMember.Parameters,{Name = param.Name, Type = param.Type.Name})
					end
					table.insert(newClass.Events,newMember)
				end
			end
		end

		for _,enum in pairs(api.Enums) do
			local newEnum = {}
			newEnum.Name = enum.Name
			newEnum.Items = {}
			newEnum.Tags = {}

			if enum.Tags then for c,tag in pairs(enum.Tags) do newEnum.Tags[tag] = true end end
			for __,item in pairs(enum.Items) do
				local newItem = {}
				newItem.Name = item.Name
				newItem.Value = item.Value
				table.insert(newEnum.Items,newItem)
			end

			enums[enum.Name] = newEnum
		end

		local function getMember(class,member)
			if not classes[class] or not classes[class][member] then return end
			local result = {}

			local currentClass = classes[class]
			while currentClass do
				for _,entry in pairs(currentClass[member]) do
					result[#result+1] = entry
				end
				currentClass = currentClass.Superclass
			end

			table.sort(result,function(a,b) return a.Name < b.Name end)
			return result
		end

		return {
			Classes = classes,
			Enums = enums,
			GetMember = getMember
		}
	end

	Main.ResetSettings = function()
		local function recur(t)
			local res = {}
			for set,val in pairs(t) do
				if type(val) == "table" and val._Recurse then
					res[set] = recur(val)
				else
					res[set] = val
				end
			end
			return res
		end
		Settings = recur(DefaultSettings)
	end

	return Main
end)()

return {
	SetDecompiler = function(callback)
		assert(callback == nil or type(callback) == "function", "SetDecompiler expects a function or nil")
		injectedDecompiler = callback
	end,

	Init = function(oldindex)
		local api, e = Main.FetchAPI() -- TODO: only request new api on roblox updates?
		if not api then
			return nil, "FetchAPI failed (" .. tostring(e) .. ")"
		end
		API = api

		env = {}
		env.writefile = writefile
		env.appendfile = appendfile
		env.getnilinstances = getnilinstances or get_nil_instances
		env.gethiddenprop = gethiddenprop or gethiddenproperty
		env.getnspval = getnspval
		env.getbspval = getbspval
		env.getpcd = getpcd or getpcdprop
		env.encodeBase64 = (syn and syn.crypt.base64.encode) or base64encode or (crypt and crypt.base64encode)
		env.lz4compress = lz4compress or (syn and syn.crypt.lz4.compress)
		env.hashmd5 = (syn and function(s) return syn.crypt.custom.hash("md5",s) end) or (crypt and function(s) return crypt.hash(s,"md5") end)

		Main.ResetSettings()
		Serializer.Init(oldindex)

		return true
	end,

	Save = function(object, filename, options)
		return Serializer.SaveInstance(object, filename, options)
	end
}
]===],
    ["main.serialization.save"] = [===[
local dex = require("main.serialization.dex_serializer")
local iri = require("main.runtime.iridium")
local st = require("main.runtime.status")
local core = require("main.runtime.core")

local save = {}

local ready = false
local fail = nil
local cache = nil
local skipcore = false

local function cached(scr)
    if not cache then return nil end
    local v = cache[scr]
    if type(v) == "string" then return true, v end
    if type(v) == "table" then
        if v.success and type(v.source) == "string" then return true, v.source end
        return false, v.error or "cached decompile failure"
    end
    return nil
end

local function start(lumen)
    if ready then return true end
    if fail then return false, fail end

    iri.get()

    dex.SetDecompiler(function(scr)
        if skipcore and core.is(scr) then return nil, "core script ignored" end
        local hit, src = cached(scr)
        if hit ~= nil then
            if hit then return src end
            return nil, tostring(src)
        end

        st.set("Decompiling", scr)
        local ok, out = pcall(function()
            return lumen:decompile(scr, { aggressive = false })
        end)

        if ok then return out end
        return nil, tostring(out)
    end)

    local ok, result, err = pcall(dex.Init)
    if not ok then
        fail = tostring(result)
        return false, fail
    end

    if result ~= true then
        fail = tostring(err or "DexSerializer.Init returned false")
        return false, fail
    end

    ready = true
    return true
end

function save.run(lumen, obj, file, opt)
    local ok, err = start(lumen)
    if not ok then
        error("LumenDecomp serializer init failed: " .. tostring(err), 2)
    end

    opt = opt or {}
    if opt.Decompile == nil then opt.Decompile = true end
    if opt.Binary == nil then opt.Binary = true end

    local old = cache
    local oldskip = skipcore
    cache = opt.SourceCache
    skipcore = opt.IgnoreCoreScripts == true

    local pass = {}
    for k, v in pairs(opt) do
        if k ~= "SourceCache" and k ~= "IgnoreCoreScripts" then pass[k] = v end
    end

    local callok, a, b = pcall(dex.Save, obj, file, pass)
    cache = old
    skipcore = oldskip

    if not callok then error(a, 2) end
    return a, b
end

function save.info()
    return {
        name = "DexSerializer",
        author = "Moon",
        blob = "60004ee8688b6c3a0b2b17bb246bb12928dd9079",
        embedded = true,
        ready = ready,
    }
end

return save
]===],
    ["main.version"] = [===[
return { name = "LumenDecomp", version = "3.2.2" }
]===],
    ["main.worker"] = [===[
local cfg = require("main.config")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:decompile(obj, opt)
    opt = cfg(opt)
    local raw = bc.fromScript(obj)
    local parsed = iri.get():Deserialize(raw, opt.iridium)
    local src = decomp.new(opt):decompileParsed(parsed)
    return src
end

return worker
]===],
}

local cache = {}
local nilv = {}
local busy = {}

local function req(name)
    local hit = cache[name]
    if hit == busy then
        error("LumenDecomp: cyclic module " .. tostring(name), 2)
    elseif hit ~= nil then
        return hit == nilv and nil or hit
    end
    local src = assert(mod[name], "LumenDecomp: missing module " .. tostring(name))
    cache[name] = busy
    local fn, err = loadstring("return function(require)\n" .. src .. "\nend", "@Lumen/" .. name)
    assert(fn, err)
    local out = fn()(req)
    cache[name] = out == nil and nilv or out
    return out
end

local api = req("main.api")
local workersrc = [=====[
assert(type(loadstring) == "function", "LumenDecomp worker requires loadstring()")

local mod = {
    ["main.analysis.dominators"] = [===[
local dom = {}

local function equal(a, b)
    for key in pairs(a) do if not b[key] then return false end end
    for key in pairs(b) do if not a[key] then return false end end
    return true
end

function dom.compute(blocks)
    local all = {}
    for _, block in ipairs(blocks) do all[block.id] = true end

    local out = {}
    for _, block in ipairs(blocks) do
        local set = {}

        if block.id == 1 then
            set[1] = true
        else
            for id in pairs(all) do set[id] = true end
        end

        out[block.id] = set
    end

    local chg = true
    while chg do
        chg = false

        for _, block in ipairs(blocks) do
            if block.id ~= 1 then
                local set = nil

                for _, pred in ipairs(block.predecessors) do
                    local predSet = out[pred]

                    if set == nil then
                        set = {}
                        for id in pairs(predSet) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not predSet[id] then set[id] = nil end
                        end
                    end
                end

                set = set or {}
                set[block.id] = true

                if not equal(out[block.id], set) then
                    out[block.id] = set
                    chg = true
                end
            end
        end
    end

    return out
end

return dom
]===],
    ["main.analysis.graph"] = [===[
local ins = require("main.bytecode.instructions")
local regs = require("main.analysis.registers")
local dom = require("main.analysis.dominators")
local loops = require("main.analysis.loops")
local post = require("main.analysis.postdom")

local graph = {}

function graph.build(proto)
    local ops = proto.Instructions
    local aux = ins.auxSlots(proto)
    local leaders = { [1] = true }
    local nexts = {}

    local function valid(pc)
        return pc >= 1 and pc <= #ops and not aux[pc]
    end

    for pc = 1, #ops do
        if not aux[pc] then
            local op = ops[pc]
            local name = ins.name(op)
            local nextPC = ins.next(proto, pc, aux)
            local successors = {}

            if name == "RETURN" then

            elseif name == "LOADB" and (op.C or 0) ~= 0 then
                local target = pc + op.C + 1
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            elseif ins.isConditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then successors[#successors + 1] = nextPC; leaders[nextPC] = true end

            elseif ins.isUnconditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            else
                if valid(nextPC) then successors[#successors + 1] = nextPC end
            end

            nexts[pc] = successors
        end
    end

    local list = {}
    for pc in pairs(leaders) do if valid(pc) then list[#list + 1] = pc end end
    table.sort(list)

    local blocks = {}
    local blockmap = {}

    for index, startPC in ipairs(list) do
        local nextLeader = list[index + 1] or (#ops + 1)
        local pcs = {}

        for pc = startPC, nextLeader - 1 do
            if not aux[pc] then
                pcs[#pcs + 1] = pc
                blockmap[pc] = index
            end
        end

        blocks[index] = {
            id = index,
            startPC = startPC,
            endPC = pcs[#pcs] or startPC,
            pcs = pcs,
            successors = {},
            predecessors = {},
        }
    end

    for _, block in ipairs(blocks) do
        local seen = {}
        for _, nextpc in ipairs(nexts[block.endPC] or {}) do
            local nextblock = blockmap[nextpc]
            if nextblock and not seen[nextblock] then
                seen[nextblock] = true
                block.successors[#block.successors + 1] = nextblock
            end
        end
    end

    for _, block in ipairs(blocks) do
        for _, successor in ipairs(block.successors) do
            blocks[successor].predecessors[#blocks[successor].predecessors + 1] = block.id
        end
    end

    local dominators = dom.compute(blocks)
    local postdom, ipdom = post.run(blocks)

    return {
        proto = proto,
        aux = aux,
        blocks = blocks,
        blockmap = blockmap,
        nexts = nexts,
        dominators = dominators,
        postdom = postdom,
        ipdom = ipdom,
        loops = loops.find(blocks, dominators),
        registerStats = regs.stats(proto, aux),
    }
end

return graph
]===],
    ["main.analysis.loops"] = [===[
local loops = {}

function loops.find(blocks, dom)
    local out = {}

    for _, latch in ipairs(blocks) do
        for _, hid in ipairs(latch.successors) do
            if dom[latch.id] and dom[latch.id][hid] then
                local set = { [hid] = true, [latch.id] = true }
                local todo = { latch.id }
                local n = 1

                while n <= #todo do
                    local id = todo[n]
                    n += 1
                    for _, pid in ipairs(blocks[id].predecessors) do
                        if not set[pid] then
                            set[pid] = true
                            if pid ~= hid then todo[#todo + 1] = pid end
                        end
                    end
                end

                local exits = {}
                local seen = {}
                for id in pairs(set) do
                    for _, sid in ipairs(blocks[id].successors) do
                        if not set[sid] and not seen[sid] then
                            seen[sid] = true
                            exits[#exits + 1] = blocks[sid].startPC
                        end
                    end
                end
                table.sort(exits)

                out[#out + 1] = {
                    header = hid,
                    latch = latch.id,
                    headerPC = blocks[hid].startPC,
                    latchPC = latch.endPC,
                    nodes = set,
                    exits = exits,
                    exitPC = #exits == 1 and exits[1] or nil,
                }
            end
        end
    end

    return out
end

return loops
]===],
    ["main.analysis.postdom"] = [===[
local post = {}

local function same(a, b)
    for k in pairs(a) do
        if not b[k] then return false end
    end
    for k in pairs(b) do
        if not a[k] then return false end
    end
    return true
end

function post.run(blocks)
    local all = {}
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = {}
    for _, b in ipairs(blocks) do
        local set = {}
        if #b.successors == 0 then
            set[b.id] = true
        else
            for id in pairs(all) do set[id] = true end
        end
        pd[b.id] = set
    end

    local dirty = true
    while dirty do
        dirty = false
        for i = #blocks, 1, -1 do
            local b = blocks[i]
            if #b.successors > 0 then
                local set
                for _, sid in ipairs(b.successors) do
                    local src = pd[sid]
                    if not set then
                        set = {}
                        for id in pairs(src) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not src[id] then set[id] = nil end
                        end
                    end
                end
                set = set or {}
                set[b.id] = true
                if not same(pd[b.id], set) then
                    pd[b.id] = set
                    dirty = true
                end
            end
        end
    end

    local ip = {}
    for _, b in ipairs(blocks) do
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        for _, id in ipairs(cand) do
            local near = true
            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    near = false
                    break
                end
            end
            if near then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip
end

return post
]===],
    ["main.analysis.registers"] = [===[
local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then
        set[value] = true
    end
end

local function range(set, first, last)
    for reg = first, last do
        add(set, reg)
    end
end

function regs.readWrite(op)
    local reads, writes = {}, {}
    local name = ins.name(op)
    local A, B, C = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL"
        or name == "GETIMPORT" or name == "NEWTABLE" or name == "DUPTABLE"
        or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, A)

    elseif name == "MOVE" then
        add(reads, B); add(writes, A)

    elseif name == "SETGLOBAL" or name == "SETUPVAL" then
        add(reads, A)

    elseif name == "GETTABLE" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "SETTABLE" then
        add(reads, A); add(reads, B); add(reads, C)

    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then
        add(reads, B); add(writes, A)

    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then
        add(reads, A); add(reads, B)

    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        add(reads, B); add(writes, A); add(writes, A + 1)

    elseif name == "CALL" or name == "CALLFB" then
        if B == 0 then add(reads, A) else range(reads, A, A + B - 1) end
        if C == 0 then add(writes, A) elseif C > 1 then range(writes, A, A + C - 2) end

    elseif name == "RETURN" then
        if B == 0 then add(reads, A) elseif B > 1 then range(reads, A, A + B - 2) end

    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV"
        or name == "MOD" or name == "POW" or name == "IDIV"
        or name == "AND" or name == "OR" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK"
        or name == "MODK" or name == "POWK" or name == "IDIVK"
        or name == "ANDK" or name == "ORK" then
        add(reads, B); add(writes, A)

    elseif name == "SUBRK" or name == "DIVRK" then
        add(reads, C); add(writes, A)

    elseif name == "CONCAT" then
        range(reads, B, C); add(writes, A)

    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
        add(reads, B); add(writes, A)

    elseif name == "SETLIST" then
        add(reads, A)
        if C == 0 then add(reads, B) elseif C > 1 then range(reads, B, B + C - 2) end

    elseif name == "FORNPREP" or name == "FORNLOOP" then
        range(reads, A, A + 3); range(writes, A + 2, A + 3)

    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, A, A + 2)

    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, A, A + 2); add(writes, A + 2)
        if count > 0 then range(writes, A + 3, A + 2 + count) end

    elseif name == "GETVARARGS" then
        if B == 0 then add(writes, A) elseif B > 1 then range(writes, A, A + B - 2) end

    elseif name == "CAPTURE" then
        if A == 0 or A == 1 then add(reads, B) end

    elseif name == "JUMPIF" or name == "JUMPIFNOT"
        or name == "JUMPXEQKNIL" or name == "JUMPXEQKB"
        or name == "JUMPXEQKN" or name == "JUMPXEQKS"
        or name == "CMPPROTO" then
        add(reads, A)

    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ"
        or name == "JUMPIFLT" or name == "JUMPIFLE"
        or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, A); add(reads, bit32.band(aux, 0xff))

    elseif name == "NEWCLASSMEMBER" then
        add(reads, A); add(reads, C)

    elseif name == "NEWCLASS" then
        if B ~= 0xff then add(reads, B) end
        add(writes, A)
    end

    return reads, writes
end

function regs.stats(proto, aux)
    local stats = {}
    aux = aux or ins.auxSlots(proto)

    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = {
                reads = 0, writes = 0,
                firstWrite = nil, lastWrite = nil,
                firstRead = nil, lastRead = nil,
                firstAccess = nil, lastAccess = nil,
            }
            stats[reg] = entry
        end
        return entry
    end

    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local op = proto.Instructions[pc]
            local reads, writes = regs.readWrite(op)

            for reg in pairs(reads) do
                local entry = get(reg)
                entry.reads += 1
                entry.firstRead = entry.firstRead or pc
                entry.lastRead = pc
                entry.firstAccess = entry.firstAccess or pc
                entry.lastAccess = pc
            end

            local name = ins.name(op)
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local entry = get(reg)
                    entry.writes += 1
                    entry.firstWrite = entry.firstWrite or pc
                    entry.lastWrite = pc
                    entry.firstAccess = entry.firstAccess or pc
                    entry.lastAccess = pc
                end
            end
        end
    end

    return stats
end

return regs
]===],
    ["main.analysis.ssa"] = [===[
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
            local _, writes = regs.readWrite(op)

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

    local changed = true
    local iterations = 0
    local maxiter = math.max(16, #cfg.blocks * 8)

    while changed and iterations < maxiter do
        iterations = iterations + 1
        changed = false

        for _, block in ipairs(cfg.blocks) do
            local incoming = merge(block)
            local oldin = result.inVersions[block.id] or {}

            if not same(oldin, incoming) then
                result.inVersions[block.id] = incoming
                changed = true
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

            local oldout = result.outVersions[block.id] or {}
            if not same(oldout, current) then
                result.outVersions[block.id] = current
                changed = true
            end
        end
    end

    result.converged = not changed
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
            local reads, _ = regs.readWrite(op)
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
]===],
    ["main.ast.booleans"] = [===[
local pass = {}

local function val(n)
    if not n or n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) or v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function neg(s)
    local x = s:match("^not%s+%((.*)%)$") or s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        local done = false
        if cur and cur.kind == "if" and #cur.branches == 1 and not cur.elsebody and nxt and nxt.kind == "return" then
            local body = cur.branches[1].body
            if #body.body == 1 then
                local a = val(body.body[1])
                local b = val(nxt)
                if a and b then
                    local x
                    if a == "true" and b == "false" then x = cur.branches[1].cond
                    elseif a == "false" and b == "true" then x = neg(cur.branches[1].cond)
                    elseif a == b then x = a
                    else x = "if " .. cur.branches[1].cond .. " then " .. a .. " else " .. b end
                    out[#out + 1] = { kind = "return", text = "return " .. x }
                    i += 2
                    done = true
                end
            end
        end
        if not done then
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.callbacks"] = [===[
local pass = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hits(s, name)
    local n = 0
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local at = 1
    while true do
        local a, b = s:find(pat, at)
        if not a then break end
        n += 1
        at = b + 1
    end
    return n
end

local function count(node, name)
    if not node or node.dead then return 0 end
    local n = 0
    if node.text then n += hits(node.text, name) end
    if node.cond then n += hits(node.cond, name) end
    if node.head then n += hits(node.head, name) end
    if node.args then n += hits(node.args, name) end
    if node.kind == "if" then
        for _, b in ipairs(node.branches) do
            n += hits(b.cond, name)
            for _, x in ipairs(b.body.body) do n += count(x, name) end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body) do n += count(x, name) end end
    elseif node.body then
        for _, x in ipairs(node.body.body) do n += count(x, name) end
    end
    return n
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
end

local function split(text, name)
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local a, b = text:find(pat)
    if not a then return nil end
    if text:find(pat, b + 1) then return nil end
    local pre = text:sub(1, a - 1)
    if not pre:find("%(") then return nil end
    return pre, text:sub(b + 1)
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        if cur and cur.kind == "function" and cur.localfn and nxt and nxt.kind == "raw"
            and count(cur, cur.name) == 0 and rest(block.body, i + 1, cur.name) == 1 then
            local pre, post = split(nxt.text, cur.name)
            if pre then
                out[#out + 1] = { kind = "callback", pre = pre, post = post, args = cur.args, body = cur.body }
                i += 2
            else
                out[#out + 1] = cur
                i += 1
            end
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.compound"] = [===[
local pass = {}

local list = {
    { "//", "//=" }, { "..", "..=" }, { "+", "+=" }, { "-", "-=" },
    { "*", "*=" }, { "/", "/=" }, { "%", "%=" }, { "^", "^=" },
}

local function pesc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function one(s)
    local name, rhs = s:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if not name then return s end
    local pre = "^" .. pesc(name) .. "%s*"
    for _, x in ipairs(list) do
        local tail = rhs:match(pre .. pesc(x[1]) .. "%s*(.+)$")
        if tail and tail ~= "" then return name .. " " .. x[2] .. " " .. tail end
    end
    return s
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "raw" then node.text = one(node.text)
        elseif node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.conditions"] = [===[
local pass = {}

local function same(a, b)
    if a == b then return true end
    if type(a) ~= type(b) or type(a) ~= "table" then return false end
    for k, v in pairs(a) do
        if k ~= "dead" and not same(v, b[k]) then return false end
    end
    for k, v in pairs(b) do
        if k ~= "dead" and a[k] == nil and v ~= nil then return false end
    end
    return true
end

local function merge(node)
    local out = {}
    for _, b in ipairs(node.branches) do
        local prev = out[#out]
        if prev and same(prev.body, b.body) then
            prev.cond = "(" .. prev.cond .. ") or (" .. b.cond .. ")"
        else
            out[#out + 1] = b
        end
    end
    node.branches = out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do
                walk(branch.body)
                local body = branch.body.body
                if #body == 1 and body[1].kind == "if" and not body[1].elsebody and #body[1].branches == 1 then
                    local sub = body[1]
                    branch.cond = "(" .. branch.cond .. ") and (" .. sub.branches[1].cond .. ")"
                    branch.body = sub.branches[1].body
                end
            end
            if node.elsebody then walk(node.elsebody) end
            merge(node)
        elseif node.body then
            walk(node.body)
        end
    end

end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.deadcode"] = [===[
local pass = {}

local function walk(block)
    local out = {}
    local done = false
    for _, node in ipairs(block.body) do
        if not node.dead and not done then
            if node.kind == "if" then
                for _, branch in ipairs(node.branches) do walk(branch.body) end
                if node.elsebody then walk(node.elsebody) end
            elseif node.body then
                walk(node.body)
            end
            out[#out + 1] = node
            if node.kind == "return" or node.kind == "break" or node.kind == "continue" then done = true end
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.fold"] = [===[
local pass = {}

local function bool(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    if s == "true" then return true end
    if s == "false" or s == "nil" then return false end
    if s == "not true" then return false end
    if s == "not false" or s == "not nil" then return true end
    return nil
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            local keep = {}
            local done = false
            for _, b in ipairs(node.branches) do
                local v = bool(b.cond)
                if v == true then
                    if #keep == 0 then
                        for _, sub in ipairs(b.body.body) do out[#out + 1] = sub end
                    else
                        node.branches = keep
                        node.elsebody = b.body
                        out[#out + 1] = node
                    end
                    done = true
                    break
                elseif v == nil then
                    keep[#keep + 1] = b
                end
            end
            if not done then
                if #keep == 0 then
                    if node.elsebody then
                        for _, sub in ipairs(node.elsebody.body) do out[#out + 1] = sub end
                    end
                else
                    node.branches = keep
                    out[#out + 1] = node
                end
            end
        elseif node.kind == "while" then
            walk(node.body)
            if bool(node.cond) ~= false then out[#out + 1] = node end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.guards2"] = [===[
local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local cmp = { " ~= ", " == ", " <= ", " >= ", " < ", " > " }

local function neg(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    for _, mid in ipairs(cmp) do
        local p = s:find(mid, 1, true)
        if p then
            local op = mid:sub(2, -2)
            local a = s:sub(1, p - 1)
            local b = s:sub(p + #mid)
            return a .. " " .. inv[op] .. " " .. b
        end
    end
    local x = s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
end

local function term(b)
    local x = b and b.body and b.body[#b.body]
    return x and (x.kind == "return" or x.kind == "break" or x.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.elsebody) and not term(node.branches[1].body) then
                out[#out + 1] = {
                    kind = "if",
                    branches = { { cond = neg(node.branches[1].cond), body = node.elsebody } },
                    elsebody = nil,
                }
                for _, x in ipairs(node.branches[1].body.body) do out[#out + 1] = x end
            else
                out[#out + 1] = node
            end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.inline"] = [===[
local pass = {}

local function init(n)
    if not n or n.kind ~= "raw" then return nil end
    local a, b = n.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+%s*=%s*(.+)$")
    if a then return a, b end
    return n.text:match("^local%s+([%a_][%w_]*)%s*=%s*(.+)$")
end

local function simple(s)
    if s == "..." or s:find("%(") then return false end
    return true
end

local function word(s, name)
    local n = 0
    for x in s:gmatch("[%a_][%w_]*") do
        if x == name then n += 1 end
    end
    return n
end

local function count(n, name)
    if not n or n.dead then return 0 end
    local out = 0
    if n.text then out += word(n.text, name) end
    if n.cond then out += word(n.cond, name) end
    if n.head then out += word(n.head, name) end
    if n.args then out += word(n.args, name) end
    if n.kind == "if" then
        for _, b in ipairs(n.branches) do
            out += word(b.cond, name)
            for _, x in ipairs(b.body.body) do out += count(x, name) end
        end
        if n.elsebody then for _, x in ipairs(n.elsebody.body) do out += count(x, name) end end
    elseif n.body then
        for _, x in ipairs(n.body.body) do out += count(x, name) end
    end
    return out
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        local name, rhs = init(cur)
        local used = name and rest(block.body, i + 1, name) or 0
        if name and nxt and used == 1 and simple(rhs) and nxt.kind == "return" and nxt.text == "return " .. name then
            out[#out + 1] = { kind = "return", text = "return " .. rhs }
            i += 2
        elseif name and nxt and used == 1 and simple(rhs) and nxt.kind == "if" and #nxt.branches > 0 then
            local c = nxt.branches[1].cond
            if c == name then
                nxt.branches[1].cond = rhs
                out[#out + 1] = nxt
                i += 2
            elseif c == "not " .. name or c == "not (" .. name .. ")" then
                nxt.branches[1].cond = "not (" .. rhs .. ")"
                out[#out + 1] = nxt
                i += 2
            else
                out[#out + 1] = cur
                i += 1
            end
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.locals"] = [===[
local pass = {}

local function walk(block)
    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end

        local nextn = block.body[i + 1]
        if node.kind == "raw" and nextn and nextn.kind == "raw" then
            local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
            if name then
                local lhs, rhs = nextn.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
                if lhs == name then
                    node.text = node.text .. " = " .. rhs
                    i += 1
                end
            end
        end
        out[#out + 1] = node
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.logic"] = [===[
local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function neg(s)
    s = trim(s)
    local x = s:match("^not%s+%((.+)%)$") or s:match("^not%s+(.+)$")
    if not x then return s end
    x = trim(x)
    local y = x:match("^not%s+%((.+)%)$") or x:match("^not%s+([%a_][%w_%.]*)$")
    if y then return trim(y) end
    for _, op in ipairs({ "~=", "==", "<=", ">=", "<", ">" }) do
        local a, b = x:match("^(.-)%s+" .. op:gsub("([^%w])", "%%%1") .. "%s+(.+)$")
        if a and b then return trim(a) .. " " .. inv[op] .. " " .. trim(b) end
    end
    return s
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do
                x.cond = neg(x.cond)
                walk(x.body)
            end
            if n.elsebody then walk(n.elsebody) end
        elseif n.kind == "while" or n.kind == "repeat" then
            n.cond = neg(n.cond)
            walk(n.body)
        elseif n.body then
            walk(n.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.lower"] = [===[
local n = require("main.ast.nodes")

local build = {}
build.__index = build

local function add(body, node)
    body.body[#body.body + 1] = node
    return node
end

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

function build.new()
    local root = n.block()
    return setmetatable({ root = root, stack = { { kind = "root", body = root } } }, build)
end

function build:body()
    return self.stack[#self.stack].body
end

function build:add(node)
    return add(self:body(), node)
end

function build:last()
    local body = self:body().body
    return body[#body]
end

function build:emit(line)
    line = trim(line)

    local cond, act = line:match("^if%s+(.+)%s+then%s+(break)%s+end$")
    if not cond then cond, act = line:match("^if%s+(.+)%s+then%s+(continue)%s+end$") end
    if cond then
        local node = n.if_(cond)
        add(node.branches[1].body, n.term(act, act))
        return self:add(node)
    end

    cond = line:match("^if%s+(.+)%s+then$")
    if cond then
        local node = self:add(n.if_(cond))
        self.stack[#self.stack + 1] = { kind = "if", node = node, body = node.branches[1].body }
        return node
    end

    cond = line:match("^elseif%s+(.+)%s+then$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray elseif")
        local branch = { cond = cond, body = n.block() }
        top.node.branches[#top.node.branches + 1] = branch
        top.body = branch.body
        return top.node
    end

    if line == "else" then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray else")
        top.node.elsebody = n.block()
        top.body = top.node.elsebody
        return top.node
    end

    cond = line:match("^while%s+(.+)%s+do$")
    if cond then
        local node = self:add(n.while_(cond))
        self.stack[#self.stack + 1] = { kind = "while", node = node, body = node.body }
        return node
    end

    if line == "repeat" then
        local node = self:add(n.repeat_())
        self.stack[#self.stack + 1] = { kind = "repeat", node = node, body = node.body }
        return node
    end

    cond = line:match("^until%s+(.+)$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "repeat", "LumenDecomp: stray until")
        top.node.cond = cond
        self.stack[#self.stack] = nil
        return top.node
    end

    local head = line:match("^(for%s+.+)%s+do$")
    if head then
        local node = self:add(n.for_(head))
        self.stack[#self.stack + 1] = { kind = "for", node = node, body = node.body }
        return node
    end

    if line == "do" then
        local node = self:add(n.do_())
        self.stack[#self.stack + 1] = { kind = "do", node = node, body = node.body }
        return node
    end

    local name, args = line:match("^local%s+function%s+([%w_]+)%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), true, false))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    name, args = line:match("^([%w_]+)%s*=%s*function%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), false, true))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    if line == "end" then
        local top = self.stack[#self.stack]
        assert(#self.stack > 1 and top.kind ~= "repeat", "LumenDecomp: stray end")
        self.stack[#self.stack] = nil
        return top.node
    end

    if line == "break" then return self:add(n.term("break", line)) end
    if line == "continue" then return self:add(n.term("continue", line)) end
    if line == "return" or line:match("^return%s") then return self:add(n.term("return", line)) end

    return self:add(n.raw(line))
end

function build:done()
    assert(#self.stack == 1, "LumenDecomp: AST builder has unclosed blocks")
    return self.root
end

return build
]===],
    ["main.ast.nodes"] = [===[
local n = {}

function n.block()
    return { kind = "block", body = {} }
end

function n.raw(s)
    return { kind = "raw", text = s }
end

function n.if_(cond)
    return { kind = "if", branches = { { cond = cond, body = n.block() } }, elsebody = nil }
end

function n.while_(cond)
    return { kind = "while", cond = cond, body = n.block() }
end

function n.repeat_()
    return { kind = "repeat", cond = "true", body = n.block() }
end

function n.for_(head)
    return { kind = "for", head = head, body = n.block() }
end

function n.do_()
    return { kind = "do", body = n.block() }
end

function n.func(name, args, body, localfn, assign)
    return { kind = "function", name = name, args = args, body = body or n.block(), localfn = localfn == true, assign = assign == true }
end

function n.term(kind, text)
    return { kind = kind, text = text }
end

return n
]===],
    ["main.ast.pipeline"] = [===[
local fold = require("main.ast.fold")
local cond = require("main.ast.conditions")
local logic = require("main.ast.logic")
local guards = require("main.recover.guards")
local guards2 = require("main.ast.guards2")
local selectp = require("main.ast.selects")
local ret = require("main.ast.returns")
local inline = require("main.ast.inline")
local callbacks = require("main.ast.callbacks")
local bools = require("main.ast.booleans")
local comp = require("main.ast.compound")
local locals = require("main.ast.locals")
local dead = require("main.ast.deadcode")

local pass = {}

function pass.run(root, opt)
    opt = opt or {}
    if opt.dce ~= false then dead.run(root) end
    if opt.fold ~= false then fold.run(root) end
    if opt.conditions ~= false then cond.run(root) end
    if opt.selects ~= false then selectp.run(root) end
    if opt.returns ~= false then ret.run(root) end
    if opt.inlineast ~= false then inline.run(root) end
    if opt.callbacks ~= false then callbacks.run(root) end
    if opt.booleans ~= false then bools.run(root) end
    if opt.guards ~= false then
        guards2.run(root)
        guards.run(root)
    end
    locals.run(root)
    if opt.compound ~= false then comp.run(root) end
    logic.run(root)
    if opt.conditions ~= false then cond.run(root) end
    if opt.dce ~= false then dead.run(root) end
    return root
end

return pass
]===],
    ["main.ast.printer"] = [===[
local printast = {}

local function line(out, depth, s)
    out[#out + 1] = string.rep("    ", depth) .. s
end

local function block(out, b, depth)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, depth, node.text)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, depth, (i == 1 and "if " or "elseif ") .. branch.cond .. " then")
                    block(out, branch.body, depth + 1)
                end
                if node.elsebody then
                    line(out, depth, "else")
                    block(out, node.elsebody, depth + 1)
                end
                line(out, depth, "end")
            elseif k == "while" then
                line(out, depth, "while " .. node.cond .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "repeat" then
                line(out, depth, "repeat")
                block(out, node.body, depth + 1)
                line(out, depth, "until " .. node.cond)
            elseif k == "for" then
                line(out, depth, node.head .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "do" then
                line(out, depth, "do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "callback" then
                line(out, depth, node.pre .. "function(" .. node.args .. ")")
                block(out, node.body, depth + 1)
                line(out, depth, "end" .. node.post)
            elseif k == "function" then
                if node.localfn then
                    line(out, depth, "local function " .. node.name .. "(" .. node.args .. ")")
                elseif node.assign then
                    line(out, depth, node.name .. " = function(" .. node.args .. ")")
                else
                    line(out, depth, "function " .. node.name .. "(" .. node.args .. ")")
                end
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            end
        end
    end
end

function printast.run(root)
    local out = {}
    block(out, root, 0)
    return table.concat(out, "\n")
end

return printast
]===],
    ["main.ast.returns"] = [===[
local pass = {}

local function ret(b)
    if not b or #b.body ~= 1 then return nil end
    local n = b.body[1]
    if n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) then return nil end
    if v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function expr(n)
    if n.kind ~= "if" or not n.elsebody or #n.branches == 0 then return nil end
    local vals = {}
    for _, b in ipairs(n.branches) do
        local v = ret(b.body)
        if not v then return nil end
        vals[#vals + 1] = { cond = b.cond, val = v }
    end
    local last = ret(n.elsebody)
    if not last then return nil end
    if #vals == 1 then
        if vals[1].val == last then return vals[1].val end
        if vals[1].val == "true" and last == "false" then return vals[1].cond end
        if vals[1].val == "false" and last == "true" then return "not (" .. vals[1].cond .. ")" end
    end
    local out = "if " .. vals[1].cond .. " then " .. vals[1].val
    for i = 2, #vals do out = out .. " elseif " .. vals[i].cond .. " then " .. vals[i].val end
    return out .. " else " .. last
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do walk(x.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end
    local out = {}
    for _, n in ipairs(b.body) do
        local x = expr(n)
        if x then out[#out + 1] = { kind = "return", text = "return " .. x }
        else out[#out + 1] = n end
    end
    b.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.ast.selects"] = [===[
local pass = {}

local function asn(node)
    if not node or node.kind ~= "raw" then return nil end
    local a, b = node.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if a then return a, b end
end

local function decl(node)
    if not node or node.kind ~= "raw" then return nil end
    local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
    return name, name and node.text or nil
end

local function pick(node)
    if node.kind ~= "if" or not node.elsebody or #node.branches == 0 then return nil end
    local name
    local parts = {}
    for _, b in ipairs(node.branches) do
        if #b.body.body ~= 1 then return nil end
        local n, v = asn(b.body.body[1])
        if not n or (name and name ~= n) then return nil end
        name = n
        parts[#parts + 1] = { cond = b.cond, val = v }
    end
    if #node.elsebody.body ~= 1 then return nil end
    local n, v = asn(node.elsebody.body[1])
    if not n or n ~= name then return nil end
    if #parts == 1 then
        if parts[1].val == v then return name, v end
        if parts[1].val == "true" and v == "false" then return name, parts[1].cond end
        if parts[1].val == "false" and v == "true" then return name, "not (" .. parts[1].cond .. ")" end
    end
    local out = "if " .. parts[1].cond .. " then " .. parts[1].val
    for i = 2, #parts do out = out .. " elseif " .. parts[i].cond .. " then " .. parts[i].val end
    out = out .. " else " .. v
    return name, out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        local name, expr = pick(node)
        local prev = out[#out]
        local dn, dp = decl(prev)
        if name and dn == name then
            prev.text = dp .. " = " .. expr
        elseif name then
            out[#out + 1] = { kind = "raw", text = name .. " = " .. expr }
        else
            out[#out + 1] = node
        end
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.bytecode.instructions"] = [===[
local ins = {}

local conditional = {
    JUMPIF = true,
    JUMPIFNOT = true,
    JUMPIFEQ = true,
    JUMPIFNOTEQ = true,
    JUMPIFLT = true,
    JUMPIFLE = true,
    JUMPIFNOTLT = true,
    JUMPIFNOTLE = true,
    JUMPXEQKNIL = true,
    JUMPXEQKB = true,
    JUMPXEQKN = true,
    JUMPXEQKS = true,
    CMPPROTO = true,
    FORNLOOP = true,
    FORGLOOP = true,
}

local jumps = {
    JUMP = true,
    JUMPBACK = true,
    JUMPX = true,
    FORGPREP = true,
    FORGPREP_INEXT = true,
    FORGPREP_NEXT = true,
}

function ins.name(op)
    return op and op.OpCodeInfo and op.OpCodeInfo.Name or "?"
end

function ins.auxSlots(proto)
    local slots = {}

    for pc = 1, #proto.Instructions do
        if not slots[pc] then
            local op = proto.Instructions[pc]
            if op and op.OpCodeInfo and op.OpCodeInfo.HasAux then
                slots[pc + 1] = true
            end
        end
    end

    return slots
end

function ins.next(proto, pc, auxSlots)
    auxSlots = auxSlots or ins.auxSlots(proto)
    local op = proto.Instructions[pc]

    if not op then
        return pc + 1
    end

    return pc + ((op.OpCodeInfo and op.OpCodeInfo.HasAux) and 2 or 1)
end

function ins.jumpTarget(pc, op)
    if ins.name(op) == "JUMPX" then
        return pc + (op.E or 0) + 1
    end

    return pc + (op.D or 0) + 1
end

function ins.isConditional(op)
    return conditional[ins.name(op)] == true
end

function ins.isUnconditional(op)
    return jumps[ins.name(op)] == true
end

function ins.previousRealPC(auxSlots, pc)
    pc = pc - 1
    while pc >= 1 do
        if not auxSlots[pc] then
            return pc
        end
        pc = pc - 1
    end
end

return ins
]===],
    ["main.config"] = [===[
local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = true,
    types = true,
    selects = true,
    returns = true,
    compound = true,
    inlineast = true,
    callbacks = true,
    booleans = true,
    iridium = nil,
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[k] = v end end
    return out
end
]===],
    ["main.decompiler.context"] = [===[
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")
local tab = require("main.recover.tables")
local ty = require("main.naming.types")

local ctx = {}
ctx.__index = ctx

function ctx.new(proto, ir, naming, up, ast, opt)
    local self = setmetatable({
        proto = proto,
        ir = ir,
        cfg = ir.cfg,
        ssa = ir.ssa,
        naming = naming,
        up = up or {},
        ast = ast,
        opt = opt or {},
        indent = 0,
        declared = {},
        namecall = {},
        consumed = {},
        alias = {},
        str = {},
        vals = {},
        expr = {},
        emit = {},
        group = {},
        tbl = {},
        top = nil,
        bad = {},
        vnames = {},
        nexttmp = 0,
    }, ctx)

    for _, name in ipairs(self.up) do naming:reserve(name) end
    for r = 0, (proto.ParameterCount or 0) - 1 do
        local v = ir.ssa.params[r]
        local name = self:vname(v, r, nil, 1)
        self.declared[name] = 0
    end
    return self
end

function ctx:out(s)
    return self.ast:emit(s)
end

function ctx:trim(depth)
    for name, d in pairs(self.declared) do
        if d >= depth then self.declared[name] = nil end
    end
end

function ctx:ann(r, pc)
    if self.opt.types == false then return nil end
    return ty.text(self.naming:typeAt(r, pc))
end

function ctx:paramann(r)
    if self.opt.types == false then return nil end
    return ty.text(ty.param(self.proto, r))
end

function ctx:badpc(pc, msg)
    local text = "pc " .. tostring(pc) .. ": " .. msg
    self.bad[#self.bad + 1] = text
    self:out("--[[ lumen: " .. text:gsub("%]%]", "] ]") .. " ]]")
end

function ctx:quiet(a, b)
    local pc = self:next(a)
    while pc < b do
        local n = self.ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = self:next(pc)
    end
    return true
end

function ctx:vname(v, r, hint, pc)
    local raw = self.ir:resolve(v)
    v = self.ir:nameid(raw)
    if not v then return self.naming:nameAt(r, pc or 1, hint) end
    local old = self.vnames[v]
    if old then return old end

    local di = pc and self.naming:debugAt(r, pc) or nil
    local ti = pc and self.naming:typeAt(r, pc) or nil
    local src = raw and self.ir.vals[raw] or nil
    local best = self.ir.bestname and self.ir.bestname[v] or nil
    local score = self.ir.namescore and self.ir.namescore[v] or 0
    local name

    if di then
        name = self.naming:nameAt(r, pc, nil)
    elseif best and score >= 80 then
        name = self.naming:unique(best)
    elseif ti then
        name = self.naming:nameAt(r, pc, hint or best)
    elseif best and score >= 55 then
        name = self.naming:unique(best)
    elseif src and src.kind == "param" then
        name = self.naming:unique(hint or (score >= 55 and best or nil) or ("arg" .. tostring(src.reg + 1)))
    elseif hint then
        name = self.naming:unique(hint)
    elseif best then
        name = self.naming:unique(best)
    else
        repeat
            name = "v" .. tostring(self.nexttmp)
            self.nexttmp += 1
        until not self.naming.used[name]
        name = self.naming:unique(name)
    end

    self.vnames[v] = name
    return name
end

function ctx:useName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:veruse(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:defName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:verdef(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:reg(r, hint, pc)
    if self.alias[r] then return self.alias[r] end
    if pc then
        local u = self:veruse(pc, r)
        if u then return self:vname(u, r, hint, pc) end
        local d = self:verdef(pc, r)
        if d then return self:vname(d, r, hint, pc) end
    end
    return self.naming:name(r, hint)
end

function ctx:atom(r, hint, pc)
    return ex.atom(self:useName(pc, r, hint), false)
end

function ctx:veruse(pc, r)
    return self.ir:use(pc, r)
end

function ctx:verdef(pc, r)
    return self.ir:def(pc, r)
end

function ctx:tblmut(use, r)
    return tab.mut(self, use, r)
end

function ctx:usetbl(v, r, pc)
    return tab.use(self, v, r, pc)
end

function ctx:usex(pc, r, hint)
    local v = self:veruse(pc, r)
    if v and self.tbl[v] then
        local node = self:usetbl(v, r, pc)
        if node then return node end
    end
    if v and self.ir.const[v] then return ex.atom(self.ir.const[v], true) end
    if v and self.vals[v] then return self.vals[v] end
    return self:atom(r, hint, pc)
end

function ctx:use(pc, r, hint)
    return ex.str(self:usex(pc, r, hint))
end

function ctx:inline(pc, r, node)
    if self.naming:isDebugAt(r, pc) then return false end
    local v = self:verdef(pc, r)
    if not v or not self.ir.inline[v] then return false end
    if self.ir.const[v] then return true end
    local u = self.ir:only(v)
    if not u or not u.pc then return false end
    if node.stable then return true end
    local defop = self.ir.bypc[pc]
    local useop = self.ir.bypc[u.pc]
    if defop and useop and (defop.name == "GETGLOBAL" or defop.name == "GETIMPORT")
        and (useop.name == "CALL" or useop.name == "CALLFB") and useop.op.A == r then
        return true
    end
    if u.pc == self:next(pc) then return true end
    return self:quiet(pc, u.pc)
end

function ctx:set(pc, r, node, hint, raw)
    local v = self:verdef(pc, r)
    if v then self.expr[v] = node end
    if v and self.ir.dead[v] then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end
    if v and self:inline(pc, r, node) then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end

    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    local fresh = depth == nil or depth > self.indent
    local stmt
    if fresh then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        stmt = self:out("local " .. name .. (an and (": " .. an) or "") .. " = " .. ex.str(node))
    else
        stmt = self:out(name .. " = " .. ex.str(node))
    end
    if v then
        self.emit[v] = { node = stmt, name = name, fresh = fresh, depth = self.indent }
        if raw ~= nil then self.str[v] = raw end
    end
    return name
end

function ctx:decl(r, hint, pc)
    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    if depth == nil or depth > self.indent then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        self:out("local " .. name .. (an and (": " .. an) or ""))
    end
    return name
end

function ctx:multi(pc, regs, rhs, hints, node)
    local list = {}
    local fresh = 0
    local new = {}
    local nodes = {}
    for i, r in ipairs(regs) do
        local name = self:defName(pc, r, hints and hints[i] or nil)
        list[i] = name
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            fresh += 1
            new[#new + 1] = name
        end
    end
    if fresh == #list then
        local typed = {}
        for i, name in ipairs(list) do
            self.declared[name] = self.indent
            local an = self:ann(regs[i], pc)
            typed[i] = name .. (an and (": " .. an) or "")
        end
        nodes[#nodes + 1] = self:out("local " .. table.concat(typed, ", ") .. " = " .. rhs)
    else
        if fresh > 0 then
            for _, name in ipairs(list) do
                local depth = self.declared[name]
                if depth == nil or depth > self.indent then
                    self.declared[name] = self.indent
                    nodes[#nodes + 1] = self:out("local " .. name)
                end
            end
        end
        nodes[#nodes + 1] = self:out(table.concat(list, ", ") .. " = " .. rhs)
    end
    if node then
        local g = { nodes = nodes, new = new, depth = self.indent, node = node }
        for _, r in ipairs(regs) do
            local v = self:verdef(pc, r)
            if v then self.group[v] = g end
        end
    end
    return list
end

function ctx:only(v, a, b, r)
    if not v then return false end
    local block = self.cfg.blockmap[b]
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then
            if u.pc ~= a and u.pc ~= b then return false end
        elseif u.phi then
            local pv = self.ir.vals[self.ir:resolve(u.phi)]
            if not pv or pv.block ~= block or pv.reg ~= r then return false end
        else
            return false
        end
    end
    return true
end

function ctx:hide(v)
    local e = v and self.emit[v]
    if not e or not e.fresh or not e.node then return false end
    e.node.dead = true
    if self.declared[e.name] == e.depth then self.declared[e.name] = nil end
    self.naming:release(e.name)
    return true
end

function ctx:loopx(pc, loop, r)
    local v = self:veruse(pc, r)
    local node = v and self.expr[v]
    if not node or not node.stable or not self:only(v, pc, loop, r) then
        return self:usex(pc, r)
    end
    if self:hide(v) then return node end
    return self:usex(pc, r)
end

function ctx:hidegroup(g, pc, loop, regs)
    if not g or not g.nodes then return false end
    for _, r in ipairs(regs) do
        local v = self:veruse(pc, r)
        if not v or self.group[v] ~= g or not self:only(v, pc, loop, r) then return false end
    end
    for _, node in ipairs(g.nodes) do if node then node.dead = true end end
    for _, name in ipairs(g.new) do
        if self.declared[name] == g.depth then self.declared[name] = nil end
        self.naming:release(name)
    end
    return true
end

function ctx:raw(pc, r)
    local v = self:veruse(pc, r)
    return v and self.str[v] or nil
end

function ctx:next(pc)
    return ins.next(self.proto, pc, self.cfg.aux)
end

function ctx:join(pc)
    local bid = self.cfg.blockmap[pc]
    local id = bid and self.cfg.ipdom[bid]
    local b = id and self.cfg.blocks[id]
    return b and b.startPC or nil
end

function ctx:phlive(v, seen)
    v = self.ir:resolve(v)
    seen = seen or {}
    if not v or seen[v] then return false end
    seen[v] = true
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then return true end
        if u.phi and self:phlive(u.phi, seen) then return true end
    end
    return false
end

function ctx:hoist(pc)
    local bid = self.cfg.blockmap[pc]
    local phis = bid and self.ir.phis[bid]
    if not phis then return end
    local list = {}
    for r, p in pairs(phis) do
        local id = self.ir:resolve(p.id)
        if id == p.id and not self.ir.dead[id] and self:phlive(id) then list[#list + 1] = { r = r, p = p } end
    end
    table.sort(list, function(a, b) return a.r < b.r end)
    for _, item in ipairs(list) do
        local name = self:vname(item.p.id, item.r, nil, pc)
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            self.declared[name] = self.indent
            self:out("local " .. name)
        end
    end
end

return ctx
]===],
    ["main.decompiler.engine"] = [===[
local irbuild = require("main.ir.build")
local irpass = require("main.passes.pipeline")
local names = require("main.naming.resolver")
local lower = require("main.ast.lower")
local astpass = require("main.ast.pipeline")
local printer = require("main.ast.printer")
local context = require("main.decompiler.context")
local ops = require("main.decompiler.ops")
local cond = require("main.recover.conditions")
local branch = require("main.recover.branches")
local loops = require("main.recover.loops")
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")

local decomp = {}
decomp.__index = decomp

local function loopused(st, r, a, b)
    local pc = a
    while pc < b do
        local uses = st.ssa.usesByPC[pc]
        if uses and uses[r] then return true end
        pc = st:next(pc)
    end
    return false
end

function decomp.new(opt)
    return setmetatable({ opt = opt or {} }, decomp)
end

function decomp:_state(proto, up, ph)
    local ir = irbuild.run(proto)
    ir.paramhints = ph or {}
    ir = irpass.run(ir, self.opt)
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    return context.new(proto, ir, naming, up, lower.new(), self.opt)
end

function decomp:_child(proto, up, ph)
    local st = self:_state(proto, up, ph)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    self:_region(st, 1, #proto.Instructions + 1, {})
    local root = astpass.run(st.ast:done(), self.opt)
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local a = op.A
    local old = st.alias[a + 3]
    local lv = st:verdef(loop, a + 3)
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, a + 3, st:next(pc), loop) and "_" or st:vname(lv, a + 3, fall, loop)
    local limit = ex.str(st:loopx(pc, loop, a))
    local step = ex.str(st:loopx(pc, loop, a + 1))
    local init = ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head = head .. ", " .. step end
    st:out(head .. " do")
    st.indent += 1
    st.alias[a + 3] = var
    st.declared[var] = st.indent
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    st.alias[a + 3] = old
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local lop = info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth = (active.loopdepth or 0) + 1
    local vars, old = {}, {}
    for i = 1, n do
        local r = op.A + 2 + i
        old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end

    local src
    local regs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A)
    local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, regs) then
        src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then
        src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then
        src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else
        src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2))
    end

    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do")
    st.indent += 1
    for i = 1, n do
        local r = op.A + 2 + i
        st.alias[r] = vars[i]
        st.declared[vars[i]] = st.indent
    end
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then")
    st.indent += 1
    local old = active.join
    active.join = info.join
    self:_region(st, info.a, info.b, active)
    active.join = old
    st:trim(st.indent)
    st.indent -= 1

    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then
            self:_emitif(st, sub, active, "elseif")
            return
        end
        st:out("else")
        st.indent += 1
        old = active.join
        active.join = info.join
        self:_region(st, info.c, info.d, active)
        active.join = old
        st:trim(st.indent)
        st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start
    active = active or {}

    while pc < stop and pc <= #st.proto.Instructions do
        if st.cfg.aux[pc] or st.consumed[pc] then
            pc += 1
        else
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then
                active["repeat:" .. tostring(pc)] = true
                st:out("repeat")
                st.indent += 1
                local prev = active.loop
                active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active)
                active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch])
                st:trim(st.indent)
                st.indent -= 1
                st:out("until " .. ex.str(x))
                active["repeat:" .. tostring(pc)] = nil
                pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then
                    st:out("while true do")
                    st.indent += 1
                    local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active)
                    active.loop = prev
                    st:trim(st.indent)
                    st.indent -= 1
                    st:out("end")
                    pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]
                    local name = ins.name(op)

                    if name == "FORNPREP" then
                        pc = self:_numfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
                        pc = self:_genfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "CMPPROTO" then
                        local target = ins.jumpTarget(pc, op)
                        local join = st:join(pc)
                        if join and target > pc and target < join and join <= stop then
                            self:_region(st, target, join, active)
                            pc = join
                        else
                            st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop = active.loop
                        local target = ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end")
                            pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then
                                pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc)
                                    st:out("while " .. ex.str(wh.cond) .. " do")
                                    st.indent += 1
                                    local prev = active.loop
                                    active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active)
                                    active.loop = prev
                                    st:trim(st.indent)
                                    st.indent -= 1
                                    st:out("end")
                                    pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then
                                        st:hoist(info.join)
                                        self:_emitif(st, info, active)
                                        pc = info.join
                                    else
                                        st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target))
                                        pc = st:next(pc)
                                    end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target = ins.jumpTarget(pc, op)
                        local loop = active.loop
                        if loop and target == loop.breakpc then
                            st:out("break")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("continue")
                            pc = st:next(pc)
                        elseif target == stop or target == active.join then
                            pc = stop
                        else
                            st:badpc(pc, "unstructured jump -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    else
                        pc = ops.run(self, st, pc)
                    end
                end
            end
        end
    end
    return pc
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    return printer.run(root), {
        cfg = st.cfg,
        ir = st.ir,
        ssa = st.ssa,
        ssaSummary = st.ssa:summary(),
        issues = st.bad,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenDecomp: parsed bytecode has no entry proto")
    self.parsed = parsed
    local src, info = self:decompileProto(proto, {})
    self.parsed = nil
    return src, info
end

return decomp
]===],
    ["main.decompiler.ops"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")
local ex = require("main.output.expr")
local func = require("main.recover.functions")
local tab = require("main.recover.tables")

local ops = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kexpr(proto, i)
    return ex.atom(lit.constant(getk(proto, i)), true)
end

local function call(st, pc, op)
    local a, b, c = op.A, op.B, op.C
    local pending = st.namecall[a]
    local first = pending and a + 2 or a + 1
    local args = {}

    if b == 0 then
        if st.top and st.top.reg >= first then
            for r = first, st.top.reg - 1 do args[#args + 1] = st:use(pc, r) end
            args[#args + 1] = ex.str(st.top.node)
        end
    else
        for r = first, a + b - 1 do args[#args + 1] = st:use(pc, r) end
    end

    local node, hint
    if pending then
        local raw = st:raw(pc, a + 2)
        node = ex.call(ex.atom(pending.obj, false), args, pending.method)
        hint = st.naming.fromMethod(pending.method, raw)
        st.namecall[a] = nil
    else
        local callee = st:usex(pc, a)
        local raw = st:raw(pc, a + 1)
        node = ex.call(callee, args)
        hint = st.naming.fromCall(ex.str(callee), raw)
    end

    st.top = nil
    local rets = c == 0 and -1 or c - 1
    if rets == 0 then
        st:out(ex.str(node))
    elseif rets == -1 then
        st.top = { reg = a, node = node }
        local v = st:verdef(pc, a)
        if v then st.vals[v] = node end
    elseif rets == 1 then
        local v = st:verdef(pc, a)
        if v and st.ir:count(v) == 0 then st:out(ex.str(node)) else st:set(pc, a, node, hint) end
    else
        local regs, hints = {}, {}
        for r = a, a + rets - 1 do
            regs[#regs + 1] = r
            hints[#hints + 1] = r == a and hint or nil
        end
        st:multi(pc, regs, ex.str(node), hints, node)
    end
end

function ops.run(d, st, pc)
    if st.consumed[pc] or st.cfg.aux[pc] then return st:next(pc) end
    local op = st.proto.Instructions[pc]
    local name = ins.name(op)
    local a, b, c, dd = op.A, op.B, op.C, op.D
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" then
    elseif name == "LOADNIL" then st:set(pc, a, ex.atom("nil", true))
    elseif name == "LOADB" then
        st:set(pc, a, ex.atom(b == 1 and "true" or "false", true))
        if c ~= 0 then return pc + c + 1 end
    elseif name == "LOADN" then st:set(pc, a, ex.atom(tostring(dd), true))
    elseif name == "LOADK" then
        local k = getk(st.proto, dd)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "LOADKX" then
        local k = getk(st.proto, aux)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "MOVE" then
        st:set(pc, a, st:usex(pc, b), nil, st:raw(pc, b))
    elseif name == "GETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:set(pc, a, ex.atom(g, false), g)
    elseif name == "SETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:out(g .. " = " .. st:use(pc, a))
    elseif name == "GETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:set(pc, a, ex.atom(u, false), u)
    elseif name == "SETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:out(u .. " = " .. st:use(pc, a))
    elseif name == "GETIMPORT" then
        local v = lit.rawStringConstant(getk(st.proto, dd)) or lit.constant(getk(st.proto, dd))
        st:set(pc, a, ex.atom(v, true), st.naming.fromImport(v))
    elseif name == "GETTABLE" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. st:use(pc, c) .. "]"))
    elseif name == "SETTABLE" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        local kv = st:veruse(pc, c)
        if t and not t.done and sv ~= tv and kv ~= tv then
            t.entries[#t.entries + 1] = { kind = "key", key = st:use(pc, c), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. st:use(pc, c) .. "] = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
        local ki = name == "GETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local suf = lit.identifier(f) and ("." .. f) or ("[" .. lit.string(f) .. "]")
        st:set(pc, a, ex.prop(st:usex(pc, b), suf), st.naming.fromField(f))
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
        local ki = name == "SETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and lit.identifier(f) and sv ~= tv then
            tab.put(t, "field", f, st:usex(pc, a))
        else
            st:out(lit.property(st:use(pc, b), f) .. " = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEN" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. tostring(c + 1) .. "]"))
    elseif name == "SETTABLEN" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and sv ~= tv then
            local idx = c + 1
            local kind = idx == #t.entries + 1 and "list" or "key"
            t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. tostring(c + 1) .. "] = " .. st:use(pc, a))
        end
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        local ki = name == "NAMECALLUDATA" and bit32.band(aux, 0xffff) or aux
        st.namecall[a] = { obj = st:use(pc, b), method = lit.rawStringConstant(getk(st.proto, ki)) or "unknownMethod" }
    elseif name == "CALL" or name == "CALLFB" then
        call(st, pc, op)
    elseif name == "RETURN" then
        if b == 1 then
            st:out("return")
        elseif b == 0 and st.top and st.top.reg >= a then
            local vals = {}
            for r = a, st.top.reg - 1 do vals[#vals + 1] = st:use(pc, r) end
            vals[#vals + 1] = ex.str(st.top.node)
            st:out("return " .. table.concat(vals, ", "))
            st.top = nil
        elseif b == 0 then
            st:badpc(pc, "MULTRET return lost stack top")
            st:out("return " .. st:use(pc, a))
        else
            local vals = {}
            for r = a, a + b - 2 do vals[#vals + 1] = st:use(pc, r) end
            st:out("return " .. table.concat(vals, ", "))
        end
    elseif name == "NEWTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then st.tbl[v] = { reg = a, entries = {}, real = real, done = false }
        else st:set(pc, a, ex.atom("{}", false)) end
    elseif name == "DUPTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then
            local entries, slots = tab.seed(getk(st.proto, dd))
            st.tbl[v] = { reg = a, entries = entries, slots = slots, real = real, done = false }
        else
            st:set(pc, a, ex.atom(lit.constant(getk(st.proto, dd)), false))
        end
    elseif name == "SETLIST" then
        local start = aux
        local tv = st:veruse(pc, a)
        local t = tv and st.tbl[tv]
        local vals = {}
        local mult = false
        if c == 0 then
            if st.top and st.top.reg >= b then
                for r = b, st.top.reg - 1 do vals[#vals + 1] = st:usex(pc, r) end
                vals[#vals + 1] = st.top.node
                mult = true
                st.top = nil
            else
                st:badpc(pc, "SETLIST MULTRET lost stack top")
            end
        else
            for i = 0, c - 2 do vals[#vals + 1] = st:usex(pc, b + i) end
        end
        local selfref = false
        for i = 1, #vals do
            local r = b + i - 1
            if st:veruse(pc, r) == tv then selfref = true break end
        end
        if t and not t.done and not selfref then
            for i, v in ipairs(vals) do
                local idx = start + i - 1
                local kind = idx == #t.entries + 1 and "list" or "key"
                t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = v }
            end
        elseif not mult then
            for i, v in ipairs(vals) do st:out(st:use(pc, a) .. "[" .. tostring(start + i - 1) .. "] = " .. ex.str(v)) end
        else
            local tmp = st.naming:unique("values")
            local args = {}
            for _, v in ipairs(vals) do args[#args + 1] = ex.str(v) end
            st:out("do")
            st.indent += 1
            st:out("local " .. tmp .. " = table.pack(" .. table.concat(args, ", ") .. ")")
            st:out("for i = 1, " .. tmp .. ".n do")
            st.indent += 1
            st:out(st:use(pc, a) .. "[" .. tostring(start) .. " + i - 1] = " .. tmp .. "[i]")
            st.indent -= 1
            st:out("end")
            st.indent -= 1
            st:out("end")
        end
    elseif name == "NEWCLOSURE" then
        local child = st.proto.Protos and st.proto.Protos[dd + 1]
        if child then local caps, nx = func.caps(st, pc, child); func.emit(d, st, pc, a, child, caps, nx)
        else st:badpc(pc, "missing NEWCLOSURE child proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "DUPCLOSURE" then
        local ck = getk(st.proto, dd)
        local child
        if d.parsed and ck and ck.__type == "Closure" then child = d.parsed.Protos[(ck.Value or 0) + 1] end
        if child then func.emit(d, st, pc, a, child, {}, st:next(pc))
        else st:badpc(pc, "missing DUPCLOSURE proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        local map = { ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//", AND = "and", OR = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], st:usex(pc, c)))
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        local map = { ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//", ANDK = "and", ORK = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], kexpr(st.proto, c)))
    elseif name == "SUBRK" or name == "DIVRK" then
        st:set(pc, a, ex.bin(kexpr(st.proto, b), name == "SUBRK" and "-" or "/", st:usex(pc, c)))
    elseif name == "CONCAT" then
        local vals = {}
        for r = b, c do vals[#vals + 1] = st:usex(pc, r) end
        st:set(pc, a, ex.join(vals, ".."))
    elseif name == "NOT" then st:set(pc, a, ex.un("not", st:usex(pc, b)))
    elseif name == "MINUS" then st:set(pc, a, ex.un("-", st:usex(pc, b)))
    elseif name == "LENGTH" then st:set(pc, a, ex.un("#", st:usex(pc, b)))
    elseif name == "GETVARARGS" then
        if b == 0 then
            st.top = { reg = a, node = ex.atom("...", false) }
            local v = st:verdef(pc, a)
            if v then st.vals[v] = st.top.node end
        elseif b == 2 then
            st:set(pc, a, ex.atom("...", false))
        else
            local regs = {}
            for r = a, a + b - 2 do regs[#regs + 1] = r end
            st:multi(pc, regs, "...")
        end
    elseif name == "CAPTURE" or name:match("^FASTCALL") then
    elseif name == "NEWCLASSMEMBER" then
        st:badpc(pc, "experimental NEWCLASSMEMBER approximated")
        local f = lit.rawStringConstant(getk(st.proto, aux)) or "member"
        st:out(lit.property(st:use(pc, a), f) .. " = " .. st:use(pc, c))
    elseif name == "NEWCLASS" then
        st:badpc(pc, "experimental NEWCLASS approximated")
        st:set(pc, a, ex.atom("{}", false))
    else
        st:badpc(pc, "unsupported opcode " .. tostring(name))
    end
    return st:next(pc)
end

return ops
]===],
    ["main.ir.block"] = [===[
local block = {}
block.__index = block

function block.new(src)
    return setmetatable({
        id = src.id,
        first = src.startPC,
        last = src.endPC,
        pcs = src.pcs,
        preds = src.predecessors,
        succs = src.successors,
        ops = {},
    }, block)
end

return block
]===],
    ["main.ir.build"] = [===[
local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local regs = require("main.analysis.registers")
local ins = require("main.bytecode.instructions")
local fx = require("main.ir.effects")
local fn = require("main.ir.function")
local val = require("main.ir.value")
local block = require("main.ir.block")

local build = {}

function build.run(proto)
    local cfg = graph.build(proto)
    local flow = ssa.build(proto, cfg)
    local out = fn.new(proto, cfg, flow)

    for id, src in ipairs(flow.versions) do
        out.vals[id] = val.new(id, src)
        if src.dead then out.dead[id] = true end
    end

    for bid, phis in pairs(flow.phisByBlock) do
        local dst = {}
        out.phis[bid] = dst
        for reg, p in pairs(phis) do
            dst[reg] = { id = p.id, reg = reg, inputs = p.inputs, missing = p.missing }
        end
    end

    for _, src in ipairs(cfg.blocks) do
        local b = block.new(src)
        out.blocks[b.id] = b
        for _, pc in ipairs(src.pcs) do
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local reads, writes = regs.readWrite(op)
            local n = {
                pc = pc,
                op = op,
                name = name,
                block = b.id,
                reads = reads,
                writes = writes,
                pure = fx.pure(name),
                drop = fx.drop(name),
                quiet = fx.quiet(name),
                effect = fx.effect(name),
                term = fx.term(name),
            }
            out.ops[#out.ops + 1] = n
            out.bypc[pc] = n
            b.ops[#b.ops + 1] = n
        end
    end

    out:reindex()
    return out
end

return build
]===],
    ["main.ir.effects"] = [===[
local fx = {}

local pure = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, GETIMPORT = true, GETGLOBAL = true,
    GETTABLE = true, GETTABLEKS = true, GETTABLEN = true, GETUDATAKS = true,
    ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true,
    IDIV = true, ADDK = true, SUBK = true, MULK = true, DIVK = true,
    MODK = true, POWK = true, IDIVK = true, SUBRK = true, DIVRK = true,
    AND = true, OR = true, ANDK = true, ORK = true, CONCAT = true,
    NOT = true, MINUS = true, LENGTH = true, NEWTABLE = true, DUPTABLE = true,
    GETVARARGS = true,
}

local drop = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, AND = true, OR = true, ANDK = true, ORK = true,
    NOT = true, NEWTABLE = true, DUPTABLE = true, GETVARARGS = true,
}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true,
    LOADKX = true, MOVE = true, GETUPVAL = true, PREPVARARGS = true,
    COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

function fx.pure(name)
    return pure[name] == true
end

function fx.drop(name)
    return drop[name] == true
end

function fx.quiet(name)
    return quiet[name] == true
end

function fx.term(name)
    return term[name] == true
end

function fx.effect(name)
    if drop[name] or quiet[name] or term[name] then return false end
    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name == "CAPTURE" then return false end
    return true
end

return fx
]===],
    ["main.ir.function"] = [===[
local fn = {}
fn.__index = fn

function fn.new(proto, cfg, flow)
    return setmetatable({
        proto = proto,
        cfg = cfg,
        ssa = flow,
        vals = {},
        blocks = {},
        ops = {},
        bypc = {},
        phis = {},
        alias = {},
        usemap = {},
        inline = {},
        dead = {},
        const = {},
    }, fn)
end

function fn:resolve(id)
    local seen = {}
    while id and self.alias[id] and not seen[id] do
        seen[id] = true
        id = self.alias[id]
    end
    return id
end

function fn:use(pc, reg)
    local uses = self.ssa.usesByPC[pc]
    return self:resolve(uses and uses[reg] or nil)
end

function fn:def(pc, reg)
    local defs = self.ssa.defsByPC[pc]
    return self:resolve(defs and defs[reg] or nil)
end

function fn:uses(id)
    id = self:resolve(id)
    return id and self.usemap[id] or nil
end

function fn:count(id)
    local uses = self:uses(id)
    return uses and #uses or 0
end

function fn:only(id)
    local uses = self:uses(id)
    return uses and #uses == 1 and uses[1] or nil
end

function fn:nameid(id)
    id = self:resolve(id)
    return id and ((self.family and self.family[id]) or id) or nil
end

function fn:reindex()
    local map = {}
    for pc, uses in pairs(self.ssa.usesByPC) do
        for reg, raw in pairs(uses) do
            local id = self:resolve(raw)
            if id then
                local list = map[id] or {}
                map[id] = list
                list[#list + 1] = { pc = pc, reg = reg, block = self.cfg.blockmap[pc] }
            end
        end
    end
    for bid, phis in pairs(self.phis) do
        for reg, p in pairs(phis) do
            if not self.dead[p.id] then
                local clean = {}
                for raw in pairs(p.inputs or {}) do
                    local id = self:resolve(raw)
                    if id and id ~= p.id then clean[id] = true end
                end
                p.inputs = clean
                for id in pairs(clean) do
                    local list = map[id] or {}
                    map[id] = list
                    list[#list + 1] = { phi = p.id, block = bid, reg = reg }
                end
            end
        end
    end
    self.usemap = map
    for id, v in pairs(self.vals) do v.uses = map[id] or {} end
end

return fn
]===],
    ["main.ir.value"] = [===[
local val = {}
val.__index = val

function val.new(id, src)
    return setmetatable({
        id = id,
        reg = src.reg,
        pc = src.pc,
        block = src.block,
        kind = src.kind,
        dead = src.dead == true,
        alias = nil,
        uses = {},
        const = nil,
        inline = false,
    }, val)
end

return val
]===],
    ["main.naming.debug_names"] = [===[
local id = require("main.naming.identifiers")

local dbg = {}

function dbg.ranges(proto)
    local out = {}
    if not (proto and proto.HasDebugInfo and proto.LocalVariables) then return out end

    for _, info in ipairs(proto.LocalVariables) do
        local reg = info.Register
        local name = id.clean(info.Name)
        if name then
            local list = out[reg] or {}
            out[reg] = list
            list[#list + 1] = {
                name = name,
                first = info.StartPc or 0,
                last = info.EndPc or math.huge,
            }
        end
    end

    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.first == b.first then return a.last < b.last end
            return a.first < b.first
        end)
    end

    return out
end

function dbg.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.first and p < info.last then
            if not best or info.first >= best.first then best = info end
        end
    end
    return best
end

return dbg
]===],
    ["main.naming.identifiers"] = [===[
local id = {}

local kw = {
    ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true,
    ["end"] = true, ["false"] = true, ["for"] = true, ["function"] = true, ["if"] = true,
    ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true, ["or"] = true,
    ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
    ["until"] = true, ["while"] = true,
}

function id.valid(value)
    return type(value) == "string"
        and value:match("^[A-Za-z_][A-Za-z0-9_]*$")
        and not kw[value]
end

function id.clean(value)
    if type(value) ~= "string" then return nil end

    value = value:gsub("[^A-Za-z0-9_]", "_")
    value = value:gsub("_+", "_")
    value = value:gsub("^_+", "")
    value = value:gsub("_+$", "")

    if value == "" then return nil end
    if value:match("^[0-9]") then value = "_" .. value end
    if kw[value] then value = value .. "Value" end

    return value
end

function id.lowerCamel(value)
    value = id.clean(value)
    if not value then return nil end

    if value:match("^[A-Z][A-Z0-9_]+$") then
        value = value:lower()
    end

    return value:sub(1, 1):lower() .. value:sub(2)
end

return id
]===],
    ["main.naming.resolver"] = [===[
local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local dbg = require("main.naming.debug_names")
local ty = require("main.naming.types")

local names = {}
names.__index = names

function names.new(stats, opt, proto)
    return setmetatable({
        used = {},
        regs = {},
        locals = {},
        stats = stats or {},
        opt = opt or {},
        proto = proto,
        debug = dbg.ranges(proto),
        typed = ty.ranges(proto),
    }, names)
end

function names:unique(base)
    base = id.clean(base) or "value"
    if not self.used[base] then
        self.used[base] = true
        return base
    end
    local n = 2
    while self.used[base .. n] do n += 1 end
    local name = base .. n
    self.used[name] = true
    return name
end

function names:stable(reg)
    local stat = self.stats[reg]
    if not stat then return true end
    return (stat.writes or 0) <= 1 or self.opt.aggressive == true
end

function names:debugAt(reg, pc)
    return dbg.at(self.debug, reg, pc)
end

function names:typeAt(reg, pc)
    return ty.at(self.typed, reg, pc)
end

function names:isDebugAt(reg, pc)
    return self:debugAt(reg, pc) ~= nil
end

function names:nameAt(reg, pc, hint)
    local info = self:debugAt(reg, pc)
    if info then
        local key = "d:" .. tostring(reg) .. ":" .. tostring(info.first) .. ":" .. tostring(info.last) .. ":" .. info.name
        local old = self.locals[key]
        if old then return old end
        local name = self:unique(info.name)
        self.locals[key] = name
        return name
    end

    local typed = self:typeAt(reg, pc)
    if typed then
        local key = "t:" .. tostring(reg) .. ":" .. tostring(typed.StartPc) .. ":" .. tostring(typed.EndPc)
        local old = self.locals[key]
        if old then return old end
        local base = hint or ty.hint(typed)
        if base then
            local name = self:unique(base)
            self.locals[key] = name
            return name
        end
    end

    if not hint and pc == 1 then
        hint = ty.hint(ty.param(self.proto, reg))
        if not hint and reg < (self.proto.ParameterCount or 0) then hint = "arg" .. tostring(reg + 1) end
    end
    return self:name(reg, hint)
end

function names:name(reg, hint)
    local old = self.regs[reg]
    if old then return old end
    local base
    if hint and self:stable(reg) then base = id.clean(hint) end
    base = base or ("v" .. tostring(reg))
    local name = self:unique(base)
    self.regs[reg] = name
    return name
end

function names:reserve(name)
    name = id.clean(name)
    if name then self.used[name] = true end
    return name
end

function names:release(name)
    if name then self.used[name] = nil end
end

names.fromImport = rbx.fromImport
names.fromField = rbx.fromField
names.fromMethod = rbx.fromMethod
names.fromCall = rbx.fromCall

return names
]===],
    ["main.naming.roblox"] = [===[
local id = require("main.naming.identifiers")
local words = require("main.naming.words")

local rbx = {}

local fields = {
    LocalPlayer = "localPlayer", Character = "character", Humanoid = "humanoid",
    HumanoidRootPart = "rootPart", PrimaryPart = "primaryPart", CurrentCamera = "camera",
    PlayerGui = "playerGui", Backpack = "backpack", PlayerScripts = "playerScripts",
    Mouse = "mouse", Parent = "parent", Position = "position", CFrame = "cframe",
    Size = "size", Name = "name", Value = "value", Enabled = "enabled",
    Visible = "visible", Health = "health", MaxHealth = "maxHealth", Team = "team",
    UserId = "userId", CharacterAdded = "characterAdded", OnClientEvent = "event",
    OnServerEvent = "event", Touched = "touched", AbsolutePosition = "position",
    AbsoluteSize = "size", AssemblyLinearVelocity = "velocity", AssemblyAngularVelocity = "angularVelocity",
}

function rbx.fromImport(path)
    if type(path) ~= "string" then return nil end
    local tail = path:match("([A-Za-z_][A-Za-z0-9_]*)$")
    if not tail then return nil end
    if path:match("^game%.") or path == tail then return id.clean(tail) end
    return id.lowerCamel(tail)
end

function rbx.fromField(field)
    return fields[field] or id.lowerCamel(field)
end

function rbx.fromMethod(method, arg)
    if method == "GetService" and arg then return id.lowerCamel(arg) end
    if method == "WaitForChild" or method == "FindFirstChild" or method == "FindFirstAncestor" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "child"
    end
    if method == "FindFirstChildOfClass" or method == "FindFirstChildWhichIsA" or method == "FindFirstAncestorOfClass" or method == "FindFirstAncestorWhichIsA" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "instance"
    end
    if method == "IsA" then
        if arg then return "is" .. arg:gsub("^%l", string.upper) end
        return "isType"
    end
    if method == "GetPlayerFromCharacter" then return "player" end
    if method == "GetPlayers" then return "playerList" end
    if method == "GetChildren" then return "children" end
    if method == "GetDescendants" then return "descendants" end
    if method == "GetMouse" then return "mouse" end
    if method == "GetPivot" then return "pivot" end
    if method == "GetAttribute" then return arg and id.lowerCamel(arg) or "attribute" end
    if method == "GetAttributes" then return "attributes" end
    if method == "GetPropertyChangedSignal" then return "signal" end
    if method == "Clone" then return "clone" end
    if method == "Connect" or method == "ConnectParallel" then return "connection" end
    if method == "Raycast" then return "raycastResult" end
    if method == "GetPartsInPart" or method == "GetPartBoundsInBox" or method == "GetPartBoundsInRadius" then return "parts" end
    if method == "JSONDecode" then return "data" end
    if method == "JSONEncode" then return "json" end
    if method == "GenerateGUID" then return "guid" end
    if method == "InvokeServer" or method == "Invoke" then return "result" end
    return words.method(method)
end

function rbx.fromCall(callee, arg)
    if callee == "Instance.new" and arg then return id.lowerCamel(arg) end
    local ctor = {
        ["Vector3.new"] = "vector", ["Vector2.new"] = "vector", ["CFrame.new"] = "cframe",
        ["CFrame.lookAt"] = "cframe", ["Color3.new"] = "color", ["Color3.fromRGB"] = "color",
        ["Color3.fromHSV"] = "color", ["UDim.new"] = "udim", ["UDim2.new"] = "udim2",
        ["UDim2.fromScale"] = "udim2", ["UDim2.fromOffset"] = "udim2",
        ["TweenInfo.new"] = "tweenInfo", ["RaycastParams.new"] = "raycastParams",
        ["OverlapParams.new"] = "overlapParams", ["Random.new"] = "random",
        ["NumberRange.new"] = "range", ["NumberSequence.new"] = "sequence",
        ["ColorSequence.new"] = "colorSequence", ["Region3.new"] = "region",
        ["Rect.new"] = "rect",
    }
    if ctor[callee] then return ctor[callee] end
    if callee == "require" then return "module" end
    if callee == "tonumber" then return "num" end
    if callee == "tostring" then return "text" end
    if callee == "typeof" or callee == "type" then return "typeName" end
    if callee == "table.clone" then return "copy" end
    if callee == "table.pack" then return "values" end
    if callee == "string.split" then return "parts" end
    if callee == "task.spawn" or callee == "task.defer" then return "thread" end
    return words.call(callee)
end

return rbx
]===],
    ["main.naming.types"] = [===[
local id = require("main.naming.identifiers")

local types = {}

local map = {
    boolean = "flag",
    number = "num",
    integer = "num",
    string = "text",
    table = "data",
    ["function"] = "fn",
    thread = "thread",
    vector = "vec",
    buffer = "buf",
    userdata = "obj",
}

function types.hint(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    return map[name] or id.lowerCamel(name:gsub("^userdata#", "obj"))
end

function types.text(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    local safe = { boolean = true, number = true, string = true, buffer = true, integer = true, any = true }
    local out
    if info.UserdataName and id.valid(info.UserdataName) then out = info.UserdataName
    elseif safe[name] then out = name end
    if not out then return nil end
    if info.IsOptional and out ~= "any" then out = out .. "?" end
    return out
end

function types.ranges(proto)
    local out = {}
    for _, info in ipairs(proto and proto.LocalTypes or {}) do
        local reg = info.Register
        local list = out[reg] or {}
        out[reg] = list
        list[#list + 1] = info
    end
    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.StartPc == b.StartPc then return a.EndPc < b.EndPc end
            return a.StartPc < b.StartPc
        end)
    end
    return out
end

function types.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.StartPc and p < info.EndPc then
            if not best or info.StartPc >= best.StartPc then best = info end
        end
    end
    return best
end

function types.param(proto, reg)
    local fn = proto and proto.FunctionType
    local list = fn and fn.ParameterTypes
    return list and list[reg + 1] or nil
end

return types
]===],
    ["main.naming.words"] = [===[
local id = require("main.naming.identifiers")

local w = {}

local bad = {
    get = true, find = true, fetch = true, load = true, read = true, make = true,
    create = true, build = true, new = true, resolve = true, compute = true,
    calc = true, clone = true, wait = true, require = true,
}

local keep = {
    is = true, has = true, can = true, should = true, did = true, was = true,
}

local function tail(s)
    if type(s) ~= "string" then return nil end
    return s:match("([%a_][%w_]*)$")
end

function w.clean(s)
    if type(s) ~= "string" then return nil end
    s = s:gsub("^_+", ""):gsub("_+$", "")
    if s == "" then return nil end
    return id.clean(id.lowerCamel(s))
end

function w.singular(s)
    s = w.clean(s)
    if not s then return nil end
    local low = s:lower()
    if low:match("ies$") and #s > 4 then return s:sub(1, -4) .. "y" end
    if low:match("sses$") or low:match("shes$") or low:match("ches$") or low:match("xes$") or low:match("zes$") then
        return s:sub(1, -3)
    end
    if low:sub(-1) == "s" and low:sub(-2) ~= "ss" and #s > 3 then return s:sub(1, -2) end
    return s
end

function w.call(s)
    s = tail(s)
    if not s then return nil end
    local lc = id.lowerCamel(s)
    for pre in pairs(bad) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then
            local c = lc:sub(n + 1, n + 1)
            if c:match("[A-Z]") or s:sub(n + 1, n + 1):match("[A-Z]") then
                return w.clean(s:sub(n + 1))
            end
        end
    end
    for pre in pairs(keep) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then return w.clean(s) end
    end
    return w.clean(s)
end

function w.method(s)
    if type(s) ~= "string" then return nil end
    if s == "Connect" then return "connection" end
    if s == "Clone" then return "clone" end
    if s == "GetChildren" then return "children" end
    if s == "GetDescendants" then return "descendants" end
    if s == "GetAttributes" then return "attributes" end
    if s == "GetAttribute" then return "attribute" end
    if s == "GetPropertyChangedSignal" then return "signal" end
    return w.call(s)
end

function w.field(s)
    return w.clean(s)
end

function w.iter(s)
    local x = w.singular(s)
    if not x or x == s and (s == "data" or s == "list" or s == "array" or s == "items") then return "item" end
    return x or "item"
end

return w
]===],
    ["main.output.expr"] = [===[
local expr = {}

local prec = {
    ["or"] = 1,
    ["and"] = 2,
    ["=="] = 3,
    ["~="] = 3,
    ["<"] = 3,
    ["<="] = 3,
    [">"] = 3,
    [">="] = 3,
    [".."] = 4,
    ["+"] = 5,
    ["-"] = 5,
    ["*"] = 6,
    ["/"] = 6,
    ["//"] = 6,
    ["%"] = 6,
    ["^"] = 8,
}

local function node(s, p, stable, kind, a, b, op)
    return { s = s, p = p or 99, stable = stable == true, kind = kind, a = a, b = b, op = op }
end

local function text(v)
    return type(v) == "table" and v.s or tostring(v)
end

local function wrap(v, p, right, op)
    if type(v) ~= "table" then return tostring(v) end
    if v.p < p then return "(" .. v.s .. ")" end
    if v.p == p then
        if p == 3 then return "(" .. v.s .. ")" end
        if op == "^" and not right then return "(" .. v.s .. ")" end
        if op == ".." and not right then return "(" .. v.s .. ")" end
        if right and op ~= "^" and op ~= ".." then return "(" .. v.s .. ")" end
    end
    return v.s
end

function expr.atom(s, stable)
    return node(s, 99, stable, "atom")
end

function expr.bin(a, op, b)
    local p = prec[op] or 5
    return node(wrap(a, p, false, op) .. " " .. op .. " " .. wrap(b, p, true, op), p, a.stable and b.stable, "bin", a, b, op)
end

function expr.un(op, a)
    local p = 7
    local s = type(a) == "table" and (a.p < p and "(" .. a.s .. ")" or a.s) or tostring(a)
    if op == "not" then
        return node("not " .. s, p, a.stable, "un", a, nil, op)
    end
    return node(op .. s, p, a.stable, "un", a, nil, op)
end

function expr.prop(a, field)
    local base = type(a) == "table" and (a.p < 9 and "(" .. a.s .. ")" or a.s) or tostring(a)
    return node(base .. field, 10, false, "prop", a, field)
end

function expr.call(fn, args, method)
    local base = type(fn) == "table" and (fn.p < 9 and "(" .. fn.s .. ")" or fn.s) or tostring(fn)
    if method then base = base .. ":" .. method end
    return node(base .. "(" .. table.concat(args, ", ") .. ")", 10, false, "call", fn, args, method)
end

function expr.join(list, op)
    local out = list[1]
    for i = 2, #list do out = expr.bin(out, op, list[i]) end
    return out
end

function expr.str(v)
    return text(v)
end

return expr
]===],
    ["main.output.literals"] = [===[
local id = require("main.naming.identifiers")

local lit = {}

function lit.identifier(value)
    return id.valid(value)
end

function lit.number(value)
    if value ~= value then return "(0 / 0)" end
    if value == math.huge then return "math.huge" end
    if value == -math.huge then return "-math.huge" end
    if value == 0 and 1 / value == -math.huge then return "-0.0" end
    return tostring(value)
end

function lit.string(value)
    return string.format("%q", value)
end

function lit.rawStringConstant(constant)
    if not constant then return nil end

    if constant.__type == "String" then
        local ok, result = pcall(buffer.tostring, constant.Value)
        if ok then return result end
    elseif constant.__type == "Import" then
        local parts = {}
        for _, item in ipairs(constant.Value) do
            local ok, result = pcall(buffer.tostring, item.Value)
            parts[#parts + 1] = ok and result or "?"
        end
        return table.concat(parts, ".")
    end

    return nil
end

local function tableKey(key)
    local raw = lit.rawStringConstant(key)
    if raw then
        if lit.identifier(raw) then
            return raw
        end
        return "[" .. lit.string(raw) .. "]"
    end

    return "[" .. lit.constant(key) .. "]"
end

function lit.constant(constant)
    if not constant then return "nil" end

    local kind = constant.__type

    if kind == "Nil" then
        return "nil"
    elseif kind == "Boolean" then
        return tostring(constant.Value)
    elseif kind == "Number" then
        return lit.number(constant.Value)
    elseif kind == "Integer" then
        local value = constant.Value
        if constant.IsNegative and type(value) == "number" and value > 0 then
            value = -value
        end
        return type(value) == "number" and lit.number(value) or tostring(value)
    elseif kind == "String" then
        return lit.string(lit.rawStringConstant(constant) or "")
    elseif kind == "Import" then
        return lit.rawStringConstant(constant) or "nil"
    elseif kind == "Vector" then
        return "Vector3.new(" .. lit.number(constant.X) .. ", " .. lit.number(constant.Y) .. ", " .. lit.number(constant.Z) .. ")"
    elseif kind == "Table" then
        return "{}"
    elseif kind == "TableWithConstants" then
        local parts = {}
        for _, pair in ipairs(constant.Value or {}) do
            local key = tableKey(pair.Key)
            local value = pair.Value and lit.constant(pair.Value) or "nil"
            parts[#parts + 1] = key .. " = " .. value
        end
        return "{ " .. table.concat(parts, ", ") .. " }"
    elseif kind == "Closure" then
        return "nil"
    elseif kind == "ClassShape" then
        return "nil"
    end

    return "nil"
end

function lit.property(base, field)
    if lit.identifier(field) then
        return base .. "." .. field
    end
    return base .. "[" .. lit.string(field or "?") .. "]"
end

return lit
]===],
    ["main.passes.conditions"] = [===[
local ins = require("main.bytecode.instructions")

local pass = {}

function pass.run(ir)
    local out = {}
    for _, n in ipairs(ir.ops) do
        if ins.isConditional(n.op) then
            out[n.pc] = {
                jump = ins.jumpTarget(n.pc, n.op),
                fall = ins.next(ir.proto, n.pc, ir.cfg.aux),
                block = n.block,
                join = ir.cfg.ipdom[n.block],
            }
        end
    end
    ir.conds = out
    return ir
end

return pass
]===],
    ["main.passes.constants"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local pass = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kval(k)
    if not k then return nil, true end
    local t = k.__type
    if t == "Nil" then return nil, true end
    if t == "Boolean" or t == "Number" then return k.Value, true end
    if t == "Integer" then
        local v = k.Value
        if k.IsNegative and type(v) == "number" and v > 0 then v = -v end
        return v, true
    end
    if t == "String" then return lit.rawStringConstant(k), true end
    return nil, false
end

local function text(v)
    local t = type(v)
    if v == nil then return "nil" end
    if t == "string" then return lit.string(v) end
    if t == "boolean" then return tostring(v) end
    if t == "number" then return lit.number(v) end
    return nil
end

local function truth(v)
    return v ~= nil and v ~= false
end

local function calc(op, a, b)
    local ok, out = pcall(function()
        if op == "ADD" or op == "ADDK" then return a + b end
        if op == "SUB" or op == "SUBK" then return a - b end
        if op == "MUL" or op == "MULK" then return a * b end
        if op == "DIV" or op == "DIVK" then return a / b end
        if op == "MOD" or op == "MODK" then return a % b end
        if op == "POW" or op == "POWK" then return a ^ b end
        if op == "IDIV" or op == "IDIVK" then return math.floor(a / b) end
        if op == "SUBRK" then return a - b end
        if op == "DIVRK" then return a / b end
        if op == "AND" or op == "ANDK" then return truth(a) and b or a end
        if op == "OR" or op == "ORK" then return truth(a) and a or b end
    end)
    return ok and out or nil, ok
end

function pass.run(ir)
    ir.constval = {}

    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local defs = ir.ssa.defsByPC[n.pc]
        local id = defs and defs[op.A] and ir:resolve(defs[op.A]) or nil
        local v, known = nil, false

        if name == "LOADNIL" then v, known = nil, true
        elseif name == "LOADB" then v, known = op.B == 1, true
        elseif name == "LOADN" then v, known = op.D, true
        elseif name == "LOADK" then v, known = kval(getk(ir.proto, op.D))
        elseif name == "LOADKX" then v, known = kval(getk(ir.proto, op.AuxValue and op.AuxValue.Value or 0))
        elseif name == "MOVE" then
            local src = ir:use(n.pc, op.B)
            if src and ir.constval[src] ~= nil then v, known = ir.constval[src].v, true
            elseif src and ir.constval[src] and ir.constval[src].nilv then v, known = nil, true end
        elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
            local src = ir:use(n.pc, op.B)
            local cv = src and ir.constval[src]
            if cv then
                local a = cv.nilv and nil or cv.v
                if name == "NOT" then v, known = not truth(a), true
                elseif name == "MINUS" and type(a) == "number" then v, known = -a, true
                elseif name == "LENGTH" and type(a) == "string" then v, known = #a, true end
            end
        elseif name == "CONCAT" then
            local out = {}
            known = true
            for r = op.B, op.C do
                local cv = ir.constval[ir:use(n.pc, r)]
                local x = cv and not cv.nilv and cv.v or nil
                if not cv or (type(x) ~= "string" and type(x) ~= "number") then known = false break end
                out[#out + 1] = tostring(x)
            end
            if known then v = table.concat(out) end
        else
            local rr = {
                ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true, IDIV = true,
                AND = true, OR = true,
            }
            local rk = {
                ADDK = true, SUBK = true, MULK = true, DIVK = true, MODK = true, POWK = true, IDIVK = true,
                ANDK = true, ORK = true,
            }
            if rr[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if av and bv then
                    v, known = calc(name, av.nilv and nil or av.v, bv.nilv and nil or bv.v)
                end
            elseif rk[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local b, bk = kval(getk(ir.proto, op.C))
                if av and bk then v, known = calc(name, av.nilv and nil or av.v, b) end
            elseif name == "SUBRK" or name == "DIVRK" then
                local a, ak = kval(getk(ir.proto, op.B))
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if ak and bv then v, known = calc(name, a, bv.nilv and nil or bv.v) end
            end
        end

        if id and known then
            ir.constval[id] = v == nil and { nilv = true } or { v = v }
            local s = text(v)
            if s then ir.const[id] = s end
        end
    end
    return ir
end

return pass
]===],
    ["main.passes.deadcode"] = [===[
local pass = {}

function pass.run(ir)
    local memo = {}
    local function live(id, seen)
        id = ir:resolve(id)
        if not id then return false end
        if memo[id] ~= nil then return memo[id] end
        seen = seen or {}
        if seen[id] then return false end
        seen[id] = true
        for _, u in ipairs(ir:uses(id) or {}) do
            if u.pc then
                memo[id] = true
                seen[id] = nil
                return true
            elseif u.phi and live(u.phi, seen) then
                memo[id] = true
                seen[id] = nil
                return true
            end
        end
        seen[id] = nil
        memo[id] = false
        return false
    end

    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and not live(id) then
            local pc = v.pc
            local op = pc and ir.bypc[pc]
            if op and (op.drop or ir.const[id] ~= nil) then ir.dead[id] = true end
        end
    end
    return ir
end

return pass
]===],
    ["main.passes.flow"] = [===[
local pass = {}

function pass.run(ir)
    ir.regions = {
        loops = ir.cfg.loops,
        ipdom = ir.cfg.ipdom,
        postdom = ir.cfg.postdom,
    }
    return ir
end

return pass
]===],
    ["main.passes.inline"] = [===[
local ins = require("main.bytecode.instructions")

local pass = {}

local function quiet(ir, a, b)
    local pc = ins.next(ir.proto, a, ir.cfg.aux)
    while pc < b do
        local n = ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = ins.next(ir.proto, pc, ir.cfg.aux)
    end
    return true
end

function pass.run(ir)
    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and v.kind == "def" then
            local u = ir:only(id)
            local n = v.pc and ir.bypc[v.pc]
            if u and u.pc and n and ir.cfg.blockmap[v.pc] == ir.cfg.blockmap[u.pc] then
                local useop = ir.bypc[u.pc]
                if n.pure and (not useop or useop.name ~= "CAPTURE") then
                    ir.inline[id] = true
                elseif n.name == "CALL" or n.name == "CALLFB" then
                    local nx = ins.next(ir.proto, v.pc, ir.cfg.aux)
                    if u.pc == nx or quiet(ir, v.pc, u.pc) then ir.inline[id] = true end
                end
            end
        end
    end
    for id in pairs(ir.const) do
        local ok = ir:count(id) > 0
        for _, u in ipairs(ir:uses(id) or {}) do
            local useop = u.pc and ir.bypc[u.pc] or nil
            if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
        end
        if ok then ir.inline[id] = true end
    end
    return ir
end

return pass
]===],
    ["main.passes.names"] = [===[
local pass = {}

function pass.run(ir)
    local parent = {}

    local function root(x)
        x = ir:resolve(x)
        if not x then return nil end
        local p = parent[x]
        if not p then parent[x] = x return x end
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end

    local function join(a, b)
        a, b = root(a), root(b)
        if a and b and a ~= b then parent[b] = a end
    end

    for id in pairs(ir.vals) do parent[id] = id end

    for _, phis in pairs(ir.phis) do
        for _, p in pairs(phis) do
            local pid = ir:resolve(p.id)
            if pid and not ir.dead[pid] and ir:count(pid) > 0 then
                for raw in pairs(p.inputs or {}) do join(pid, raw) end
            end
        end
    end

    local fam = {}
    for id in pairs(ir.vals) do fam[id] = root(id) end
    ir.family = fam
    return ir
end

return pass
]===],
    ["main.passes.pipeline"] = [===[
local simp = require("main.passes.simplify")
local konst = require("main.passes.constants")
local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt)
    opt = opt or {}
    simp.run(ir)
    if opt.fold ~= false then konst.run(ir) end
    if opt.dce ~= false then dead.run(ir) end
    names.run(ir)
    prov.run(ir)
    if opt.inline ~= false then inline.run(ir) end
    cond.run(ir)
    flow.run(ir)
    return ir
end

return pipe
]===],
    ["main.passes.provenance"] = [===[
local lit = require("main.output.literals")
local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local ty = require("main.naming.types")
local dbg = require("main.naming.debug_names")
local words = require("main.naming.words")
local ins = require("main.bytecode.instructions")

local pass = {}

local weak = {
    value = true, result = true, data = true, item = true, obj = true,
    num = true, text = true, flag = true, fn = true,
}

local owner = {
    Character = "player", Backpack = "player", PlayerGui = "player", PlayerScripts = "player",
    UserId = "player", Team = "player", TeamColor = "player", AccountAge = "player",
    Humanoid = "character", HumanoidRootPart = "character", PrimaryPart = "model",
    Health = "humanoid", MaxHealth = "humanoid", WalkSpeed = "humanoid", JumpPower = "humanoid",
    HipHeight = "humanoid", MoveDirection = "humanoid", FloorMaterial = "humanoid",
    CFrame = "part", Position = "part", Orientation = "part", Anchored = "part",
    CanCollide = "part", AssemblyLinearVelocity = "part", AssemblyAngularVelocity = "part",
    CameraType = "camera", CameraSubject = "camera", ViewportSize = "camera",
    AbsolutePosition = "gui", AbsoluteSize = "gui", BackgroundColor3 = "gui", Text = "gui",
    UserInputType = "input", KeyCode = "input", UserInputState = "input", Delta = "input",
    OnClientEvent = "remoteEvent", OnServerEvent = "remoteEvent",
}

local methown = {
    Kick = "player", GetMouse = "player", LoadCharacter = "player",
    MoveTo = "humanoid", TakeDamage = "humanoid", ChangeState = "humanoid",
    Raycast = "workspace", GetPartsInPart = "workspace", GetPartBoundsInBox = "workspace",
    Connect = "signal", ConnectParallel = "signal", Once = "signal", Wait = "signal",
    FireServer = "remoteEvent", FireClient = "remoteEvent", FireAllClients = "remoteEvent",
    InvokeServer = "remoteFunction", InvokeClient = "remoteFunction",
    GetPlayers = "players", GetPlayerFromCharacter = "players",
    GetTagged = "collectionService", HasTag = "collectionService", AddTag = "collectionService", RemoveTag = "collectionService",
    JSONDecode = "httpService", JSONEncode = "httpService", GenerateGUID = "httpService",
}

local function getk(proto, n)
    return proto.Constants and proto.Constants[(n or 0) + 1]
end

local function rawk(proto, n)
    return lit.rawStringConstant(getk(proto, n))
end

local function cv(ir, v)
    v = ir:resolve(v)
    local x = v and ir.constval and ir.constval[v]
    if not x then return nil, false end
    return x.nilv and nil or x.v, true
end

function pass.run(ir)
    local hints = {}
    local origin = {}
    local pend = {}
    local dr = dbg.ranges(ir.proto)
    local tr = ty.ranges(ir.proto)

    local function fam(v)
        return v and ir:nameid(v) or nil
    end

    local function add(v, name, score, why)
        v = fam(v)
        name = id.clean(name)
        if not v or not name then return end
        if weak[name] then score -= 8 end
        local h = hints[v]
        if not h then h = {}; hints[v] = h end
        local old = h[name]
        if not old then
            h[name] = { score = score, why = why, hits = 1 }
        else
            old.hits = (old.hits or 1) + 1
            if score > old.score then old.score, old.why = score, why end
        end
    end

    local function seto(v, path, kind)
        v = ir:resolve(v)
        if v and path then origin[v] = { path = path, kind = kind } end
    end

    local function geto(v)
        v = ir:resolve(v)
        return v and origin[v] or nil
    end

    local function opname(v)
        v = ir:resolve(v)
        local x = v and ir.vals[v]
        local n = x and x.pc and ir.bypc[x.pc]
        return n and n.name or nil
    end

    for v, src in pairs(ir.vals) do
        if src.kind == "param" and ir.paramhints then add(v, ir.paramhints[src.reg + 1], 118, "context") end
        local p = src.kind == "param" and ty.param(ir.proto, src.reg) or nil
        if p then add(v, ty.hint(p), 74, "ptype") end
        local di = src.pc and dbg.at(dr, src.reg, src.pc) or nil
        if di then add(v, di.name, 120, "debug") end
        local ti = src.pc and ty.at(tr, src.reg, src.pc) or nil
        if ti then add(v, ty.hint(ti), 78, "type") end
    end

    local prep = {}
    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local pc = n.pc
        local defs = ir.ssa.defsByPC[pc] or {}
        local uses = ir.ssa.usesByPC[pc] or {}
        local function d(r) return ir:resolve(defs[r]) end
        local function u(r) return ir:resolve(uses[r]) end

        if name == "GETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            add(d(op.A), g, 104, "global")
            seto(d(op.A), g, "global")
        elseif name == "GETIMPORT" then
            local k = getk(ir.proto, op.D)
            local p = lit.rawStringConstant(k) or lit.constant(k)
            add(d(op.A), rbx.fromImport(p) or words.call(p), 108, "import")
            seto(d(op.A), p, "import")
        elseif name == "GETUPVAL" then
            local up = ir.proto.Upvalues and ir.proto.Upvalues[op.B + 1]
            local un = up and up.Name
            add(d(op.A), un, 112, "upvalue")
            seto(d(op.A), un, "upvalue")
        elseif name == "MOVE" then
            local so = geto(u(op.B))
            if so then
                seto(d(op.A), so.path, so.kind)
                add(d(op.A), words.call(so.path) or words.field(so.path), 76, "move")
            end
        elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "GETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            add(d(op.A), rbx.fromField(f) or words.field(f), 91, "field")
            add(u(op.B), owner[f], 70, "owner")
            local so = geto(u(op.B))
            if so and f then seto(d(op.A), so.path .. "." .. f, "field") else seto(d(op.A), f, "field") end
        elseif name == "GETTABLEN" then
            local so = geto(u(op.B))
            if so then add(d(op.A), words.iter(words.call(so.path) or so.path), 64, "index") end
        elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "SETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 116 or 44
            add(u(op.A), rbx.fromField(f) or words.field(f), sc, "store")
        elseif name == "SETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 120 or 38
            add(u(op.A), g, sc, "gstore")
        elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "NAMECALLUDATA" then ai = bit32.band(ai, 0xffff) end
            local m = rawk(ir.proto, ai)
            pend[op.A] = { method = m, obj = u(op.B), pc = pc }
            add(u(op.B), methown[m], 72, "method-owner")
        elseif name == "CALL" or name == "CALLFB" then
            local p = pend[op.A]
            local out = d(op.A)
            local callpath
            if p then
                local arg
                if (op.B or 0) == 0 or op.B > 2 then arg = select(1, cv(ir, u(op.A + 2))) end
                local oo = geto(p.obj)
                local base = oo and oo.path or nil
                local h = rbx.fromMethod(p.method, arg) or words.method(p.method)
                if p.method == "Create" and base and base:match("TweenService$") then h = "tween" end
                if p.method == "Clone" and base then
                    local tail = base:match("([%a_][%w_]*)$")
                    if tail then h = words.clean(tail .. "Clone") end
                end
                if p.method == "Connect" or p.method == "ConnectParallel" or p.method == "Once" then h = "connection" end
                if p.method == "Wait" and base and base:match("Signal$") then h = "value" end
                add(out, h, 106, "method")
                if p.method == "GetPlayerFromCharacter" then
                    add(u(op.A + 2), "character", 88, "arg")
                elseif p.method == "Create" and base and base:match("TweenService$") then
                    add(u(op.A + 2), "instance", 62, "arg")
                    add(u(op.A + 3), "tweenInfo", 78, "arg")
                    add(u(op.A + 4), "properties", 72, "arg")
                elseif p.method == "Raycast" then
                    add(u(op.A + 2), "origin", 66, "arg")
                    add(u(op.A + 3), "direction", 72, "arg")
                    add(u(op.A + 4), "params", 58, "arg")
                elseif p.method == "AddTag" or p.method == "RemoveTag" or p.method == "HasTag" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "tag", 72, "arg")
                elseif p.method == "AddItem" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "lifetime", 68, "arg")
                end
                local path
                if p.method == "GetService" and arg then
                    path = tostring(arg)
                elseif (p.method == "WaitForChild" or p.method == "FindFirstChild" or p.method == "FindFirstAncestor") and arg then
                    path = base and (base .. "." .. tostring(arg)) or tostring(arg)
                elseif (p.method == "FindFirstChildOfClass" or p.method == "FindFirstChildWhichIsA") and arg then
                    path = tostring(arg)
                else
                    path = base
                    if p.method then path = path and (path .. ":" .. p.method) or p.method end
                end
                callpath = path
                seto(out, path, "call")
                pend[op.A] = nil
            else
                local cal = u(op.A)
                local co = geto(cal)
                local arg
                if (op.B or 0) == 0 or op.B > 1 then arg = select(1, cv(ir, u(op.A + 1))) end
                local path = co and co.path or nil
                local h = rbx.fromCall(path, arg) or words.call(path) or "result"
                local first = {
                    pcall = "success", xpcall = "success", ["coroutine.resume"] = "success",
                    next = "key", ["string.find"] = "startPos", ["math.modf"] = "integer",
                    ["math.frexp"] = "mantissa",
                }
                h = first[path] or h
                if path == "require" then
                    local ao = geto(u(op.A + 1))
                    local tail = ao and ao.path and ao.path:match("([%a_][%w_]*)$")
                    if tail and tail ~= "Parent" then h = words.clean(tail) end
                end
                callpath = path
                add(out, h, path == "require" and 112 or 98, "call")
                add(cal, "fn", 48, "callee")
                seto(out, path, "call")
                if path == "table.insert" then
                    add(u(op.A + 1), "list", 52, "arg")
                    add(u(op.A + 2), "item", 46, "arg")
                elseif path == "pairs" or path == "ipairs" or path == "next" then
                    add(u(op.A + 1), "items", 44, "arg")
                elseif path == "pcall" or path == "xpcall" then
                    add(u(op.A + 1), "fn", 66, "arg")
                elseif path == "task.spawn" or path == "task.defer" or path == "task.delay" then
                    local r = path == "task.delay" and op.A + 2 or op.A + 1
                    add(u(r), "callback", 68, "arg")
                elseif path == "assert" then
                    add(u(op.A + 1), "condition", 48, "arg")
                end
            end
            if (op.C or 0) > 2 then
                local multi = {
                    pcall = { "success", "result" },
                    xpcall = { "success", "result" },
                    ["coroutine.resume"] = { "success", "result" },
                    next = { "key", "value" },
                    ["string.find"] = { "startPos", "endPos" },
                    ["math.modf"] = { "integer", "fraction" },
                    ["math.frexp"] = { "mantissa", "exponent" },
                }
                local set = multi[callpath]
                for r = op.A, op.A + op.C - 2 do
                    local i = r - op.A + 1
                    local h = set and set[i] or (i == 1 and nil or ("result" .. tostring(i)))
                    if h then add(d(r), h, set and 96 or 35, "multi") end
                end
            end
        elseif name == "NEWTABLE" or name == "DUPTABLE" then
            add(d(op.A), "data", 28, "table")
            seto(d(op.A), "data", "table")
        elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = ir.proto.Protos and ir.proto.Protos[(op.D or 0) + 1]
            add(d(op.A), child and child.Name or "fn", 88, "closure")
        elseif name == "NOT" then
            local so = geto(u(op.B))
            if so then add(d(op.A), "not" .. ((words.call(so.path) or "value"):gsub("^%l", string.upper)), 52, "bool") end
        elseif name == "LENGTH" then
            local so = geto(u(op.B))
            if so then
                local x = words.call(so.path)
                if x then add(d(op.A), x .. "Count", 66, "len") else add(d(op.A), "count", 54, "len") end
            else
                add(d(op.A), "count", 48, "len")
            end
        elseif name == "FORGPREP" or name == "FORGPREP_NEXT" or name == "FORGPREP_INEXT" then
            local target = ins.jumpTarget(pc, op)
            local so = geto(u(op.A + 1)) or geto(u(op.A))
            prep[target] = so and (words.call(so.path) or words.field(so.path)) or nil
        elseif name == "FORGLOOP" then
            local nvar = math.max(1, bit32.band(op.AuxValue and op.AuxValue.Value or 0, 0xff))
            local src = prep[pc]
            for i = 1, nvar do
                local v = d(op.A + 2 + i)
                if i == 1 and nvar == 1 then add(v, words.iter(src), 86, "iter")
                elseif i == 1 then add(v, "key", 68, "iter")
                elseif i == 2 then add(v, words.iter(src) or "value", 82, "iter")
                else add(v, "value" .. tostring(i), 48, "iter") end
            end
        elseif name == "FORNLOOP" then
            add(d(op.A + 3), "i", 62, "numfor")
        end
    end

    for _, n in ipairs(ir.ops) do
        local op, pc, name = n.op, n.pc, n.name
        local uses = ir.ssa.usesByPC[pc] or {}
        local function u(r) return ir:resolve(uses[r]) end
        if name == "JUMPIF" or name == "JUMPIFNOT" then
            add(u(op.A), "enabled", 38, "condition")
        elseif name == "GETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "SETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "CONCAT" then
            for r = op.B, op.C do add(u(r), "text", 30, "concat") end
        elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
            add(u(op.B), "num", 24, "math")
            add(u(op.C), "num", 24, "math")
        end
    end

    local best, score = {}, {}
    for v, set in pairs(hints) do
        for name, h in pairs(set) do
            local rank = h.score + math.min(20, math.max(0, (h.hits or 1) - 1) * 4)
            if not score[v] or rank > score[v] or (rank == score[v] and name < best[v]) then
                best[v], score[v] = name, rank
            end
        end
    end

    ir.hints = hints
    ir.bestname = best
    ir.namescore = score
    ir.origin = origin
    return ir
end

return pass
]===],
    ["main.passes.simplify"] = [===[
local pass = {}

function pass.run(ir)
    local changed = true
    while changed do
        changed = false
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                if not ir.dead[p.id] and not p.missing then
                    local one
                    local many = false
                    for raw in pairs(p.inputs or {}) do
                        local id = ir:resolve(raw)
                        if id and id ~= p.id then
                            if one and one ~= id then many = true break end
                            one = id
                        end
                    end
                    if one and not many then
                        ir.alias[p.id] = one
                        ir.dead[p.id] = true
                        ir.vals[p.id].dead = true
                        changed = true
                    end
                end
            end
        end
    end
    ir:reindex()
    return ir
end

return pass
]===],
    ["main.recover.branches"] = [===[
local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local join = st:join(pc)
    if not join or join <= pc or join > stop then join = ch.exit end
    if ch.exit > join then return nil end

    if ch.exit == join then
        return { cond = ch.cond, a = ch.body, b = join, join = join }
    end

    return { cond = ch.cond, a = ch.body, b = ch.exit, c = ch.exit, d = join, join = join }
end

function branch.elseifInfo(st, pc, join)
    local op = st.proto.Instructions[pc]
    if not op or not ins.isConditional(op) then return nil end
    local sub = branch.info(st, pc, join)
    if sub and sub.join == join then return sub end
end

return branch
]===],
    ["main.recover.conditions"] = [===[
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")

local cond = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kexpr(proto, i)
    return ex.atom(lit.constant(getk(proto, i)), true)
end

function cond.jump(st, pc, op)
    local name = ins.name(op)
    local a = st:usex(pc, op.A)
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "JUMPIF" then return a end
    if name == "JUMPIFNOT" then return ex.un("not", a) end

    local b = st:usex(pc, bit32.band(aux, 0xff))
    local cmp = {
        JUMPIFEQ = "==", JUMPIFNOTEQ = "~=", JUMPIFLT = "<",
        JUMPIFLE = "<=", JUMPIFNOTLT = ">=", JUMPIFNOTLE = ">",
    }
    if cmp[name] then return ex.bin(a, cmp[name], b) end

    if name == "JUMPXEQKNIL" then
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", ex.atom("nil", true))
    elseif name == "JUMPXEQKB" then
        local v = bit32.band(aux, 1) == 1 and "true" or "false"
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", ex.atom(v, true))
    elseif name == "JUMPXEQKN" or name == "JUMPXEQKS" then
        local k = kexpr(st.proto, bit32.band(aux, 0xffffff))
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "~=" or "==", k)
    end

    return ex.atom("true", true)
end

function cond.fall(st, pc, op)
    local name = ins.name(op)
    local a = st:usex(pc, op.A)
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "JUMPIF" then return ex.un("not", a) end
    if name == "JUMPIFNOT" then return a end

    local b = st:usex(pc, bit32.band(aux, 0xff))
    local cmp = {
        JUMPIFEQ = "~=", JUMPIFNOTEQ = "==", JUMPIFLT = ">=",
        JUMPIFLE = ">", JUMPIFNOTLT = "<", JUMPIFNOTLE = "<=",
    }
    if cmp[name] then return ex.bin(a, cmp[name], b) end

    if name == "JUMPXEQKNIL" then
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", ex.atom("nil", true))
    elseif name == "JUMPXEQKB" then
        local v = bit32.band(aux, 1) == 1 and "true" or "false"
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", ex.atom(v, true))
    elseif name == "JUMPXEQKN" or name == "JUMPXEQKS" then
        local k = kexpr(st.proto, bit32.band(aux, 0xffffff))
        return ex.bin(a, bit32.btest(aux, 0x80000000) and "==" or "~=", k)
    end

    return ex.un("not", cond.jump(st, pc, op))
end

function cond.chain(st, pc)
    local first = st.proto.Instructions[pc]
    if not ins.isConditional(first) then return nil end

    local exit = ins.jumpTarget(pc, first)
    local cur = pc
    local list = {}
    local count = 0

    while true do
        local op = st.proto.Instructions[cur]
        local name = ins.name(op)
        if not ins.isConditional(op) or name == "FORNLOOP" or name == "FORGLOOP" then break end
        if ins.jumpTarget(cur, op) ~= exit then break end
        list[#list + 1] = cond.fall(st, cur, op)
        count += 1
        local nx = st:next(cur)
        local nop = st.proto.Instructions[nx]
        if not nop or not ins.isConditional(nop) then
            return { cond = ex.join(list, "and"), body = nx, exit = exit, last = cur }
        end
        if ins.jumpTarget(nx, nop) ~= exit then break end
        cur = nx
    end

    if count > 1 then
        return { cond = ex.join(list, "and"), body = st:next(cur), exit = exit, last = cur }
    end

    local body = exit
    local p = pc
    local ors = {}
    while p < body do
        local op = st.proto.Instructions[p]
        if not op or not ins.isConditional(op) then break end
        local nx = st:next(p)
        local jt = ins.jumpTarget(p, op)
        if jt == body and nx < body then
            ors[#ors + 1] = cond.jump(st, p, op)
            p = nx
        elseif nx == body and jt > body then
            ors[#ors + 1] = cond.fall(st, p, op)
            return { cond = ex.join(ors, "or"), body = body, exit = jt, last = p }
        else
            break
        end
    end

    return { cond = cond.fall(st, pc, first), body = st:next(pc), exit = exit, last = pc }
end

function cond.bool(st, pc, op)
    if not ins.isConditional(op) then return nil end
    local fp = st:next(pc)
    local tp = ins.jumpTarget(pc, op)
    local fo = st.proto.Instructions[fp]
    local to = st.proto.Instructions[tp]
    if not fo or not to or ins.name(fo) ~= "LOADB" or ins.name(to) ~= "LOADB" or fo.A ~= to.A then return nil end

    local x
    if fo.B == 0 and to.B == 1 then
        x = cond.jump(st, pc, op)
    elseif fo.B == 1 and to.B == 0 then
        x = cond.fall(st, pc, op)
    else
        return nil
    end

    local join
    if fo.C ~= 0 then join = fp + fo.C + 1 else join = st:next(fp) end
    if join <= tp then join = st:next(tp) end
    st.consumed[fp] = true
    st.consumed[tp] = true
    local bid = st.cfg.blockmap[join]
    local phis = bid and st.ir.phis[bid]
    local phi = phis and phis[fo.A]
    if phi and not phi.missing then
        local id = st.ir:resolve(phi.id)
        st.vals[id] = x
        st.expr[id] = x
    else
        st:set(fp, fo.A, x)
    end
    return join
end

return cond
]===],
    ["main.recover.functions"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local fn = {}

local evt = {
    PlayerAdded = { "player" }, PlayerRemoving = { "player" },
    CharacterAdded = { "character" }, CharacterRemoving = { "character" },
    ChildAdded = { "child" }, ChildRemoved = { "child" },
    DescendantAdded = { "descendant" }, DescendantRemoving = { "descendant" },
    Touched = { "hit" }, TouchEnded = { "hit" },
    InputBegan = { "input", "gameProcessed" }, InputChanged = { "input", "gameProcessed" }, InputEnded = { "input", "gameProcessed" },
    Heartbeat = { "dt" }, RenderStepped = { "dt" }, PreRender = { "dt" }, PreSimulation = { "dt" }, PostSimulation = { "dt" },
    Stepped = { "time", "dt" },
    AncestryChanged = { "child", "parent" }, AttributeChanged = { "attribute" },
    Changed = { "value" },
}

local meth = {
    BindToRenderStep = { "dt" },
    BindAction = { "actionName", "inputState", "input" },
    BindActionAtPriority = { "actionName", "inputState", "input" },
}

local function cbhints(st, pc, r)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local call
    for _, u in ipairs(st.ir:uses(v) or {}) do
        if u.pc then
            if call then return nil end
            call = u.pc
        end
    end
    if not call then return nil end
    local op = st.proto.Instructions[call]
    local name = ins.name(op)
    if name ~= "CALL" and name ~= "CALLFB" then return nil end
    local pend = st.namecall[op.A]
    if pend and (pend.method == "Connect" or pend.method == "ConnectParallel" or pend.method == "Once") then
        local tail = pend.obj and pend.obj:match("([%a_][%w_]*)$")
        return tail and evt[tail] or nil
    end
    if pend and meth[pend.method] then return meth[pend.method] end
    return nil
end

function fn.caps(st, pc, child)
    local out = {}
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        local du = child.Upvalues and child.Upvalues[i]
        local dn = du and du.Name
        if ins.name(op) ~= "CAPTURE" then
            out[i] = dn or ("upvalue" .. tostring(i - 1))
        else
            local kind, src = op.A, op.B
            if dn and dn ~= "" then out[i] = dn
            elseif kind == 0 or kind == 1 then out[i] = st:useName(cp, src, nil)
            else out[i] = st.up[src + 1] or ("upvalue" .. tostring(src)) end
            st.consumed[cp] = true
            nx = st:next(cp)
        end
    end
    return out, nx
end

local function direct(st, pc, r, nx)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local uses = st.ir:uses(v) or {}
    local one
    for _, u in ipairs(uses) do
        if u.pc then
            if one then return nil end
            one = u
        end
    end
    if not one or one.pc ~= nx then return nil end
    local op = st.proto.Instructions[one.pc]
    local name = ins.name(op)
    if name == "SETGLOBAL" and op.A == r then
        local k = op.AuxValue and op.AuxValue.Value or 0
        local g = lit.rawStringConstant(st.proto.Constants and st.proto.Constants[k + 1])
        if g and lit.identifier(g) then return g, false, one.pc end
    elseif (name == "SETTABLEKS" or name == "SETUDATAKS") and op.A == r then
        local k = op.AuxValue and op.AuxValue.Value or 0
        if name == "SETUDATAKS" then k = bit32.band(k, 0xffff) end
        local f = lit.rawStringConstant(st.proto.Constants and st.proto.Constants[k + 1])
        local base = st:use(one.pc, op.B)
        if f and lit.identifier(f) then return base .. "." .. f, false, one.pc end
        if f then return lit.property(base, f), true, one.pc end
    end
end

function fn.emit(d, st, pc, r, child, caps, nx)
    local hint = child.Name
    if hint == nil or hint == "" then hint = st.ir.bestname and st.ir.bestname[st.ir:nameid(st:verdef(pc, r))] end
    if hint == nil or hint == "" then hint = "fn" .. tostring(r) end

    local root, sub, args = d:_child(child, caps, cbhints(st, pc, r))
    local target, assign, store = direct(st, pc, r, nx or st:next(pc))
    if target then
        st.consumed[store] = true
        if not assign and target:find("%.") and args[1] and args[1]:match("^self%s*[:$]") then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then
                target = base .. ":" .. field
                table.remove(args, 1)
            end
        elseif not assign and target:find("%.") and args[1] == "self" then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then
                target = base .. ":" .. field
                table.remove(args, 1)
            end
        end
        st.ast:add({ kind = "function", name = target, args = table.concat(args, ", "), body = root, localfn = false, assign = assign })
    else
        local name = st:defName(pc, r, hint)
        local depth = st.declared[name]
        if depth == nil or depth > st.indent then
            st.declared[name] = st.indent
            st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = true, assign = false })
        else
            st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = false, assign = true })
        end
    end
    for _, issue in ipairs(sub.bad) do st.bad[#st.bad + 1] = issue end
end

return fn
]===],
    ["main.recover.guards"] = [===[
local pass = {}

local function term(block)
    local body = block and block.body
    local last = body and body[#body]
    return last and (last.kind == "return" or last.kind == "break" or last.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.branches[1].body) then
                local rest = node.elsebody.body
                node.elsebody = nil
                out[#out + 1] = node
                for _, sub in ipairs(rest) do out[#out + 1] = sub end
            else
                out[#out + 1] = node
            end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
]===],
    ["main.recover.loops"] = [===[
local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local loops = {}

function loops.whileInfo(st, pc)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local latch = ins.previousRealPC(st.cfg.aux, ch.exit)
    if not latch then return nil end
    local op = st.proto.Instructions[latch]
    local name = ins.name(op)
    if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(latch, op) <= pc then
        return { cond = ch.cond, body = ch.body, bodyend = latch, exit = ch.exit, cont = pc }
    end
end

function loops.repeatInfo(st, pc)
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc then
            local op = st.proto.Instructions[loop.latchPC]
            if ins.isConditional(op) and ins.jumpTarget(loop.latchPC, op) == pc then
                return { body = pc, latch = loop.latchPC, exit = st:next(loop.latchPC), cont = loop.latchPC }
            end
        end
    end
end

function loops.foreverInfo(st, pc, stop)
    local head = st.proto.Instructions[pc]
    if ins.isConditional(head) then return nil end
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc and loop.latchPC < stop then
            local op = st.proto.Instructions[loop.latchPC]
            local name = ins.name(op)
            if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(loop.latchPC, op) == pc then
                local exit = loop.exitPC
                if not exit then
                    for _, ep in ipairs(loop.exits or {}) do
                        if ep > loop.latchPC and (not exit or ep < exit) then exit = ep end
                    end
                end
                exit = exit or st:next(loop.latchPC)
                return { body = pc, latch = loop.latchPC, exit = exit, cont = pc }
            end
        end
    end
end

function loops.numInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORNLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

function loops.genInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORGLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

return loops
]===],
    ["main.recover.tables"] = [===[
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")
local ex = require("main.output.expr")

local tab = {}

local function key(k)
    local raw = lit.rawStringConstant(k)
    if raw then
        if lit.identifier(raw) then return "field", raw end
        return "key", lit.string(raw)
    end
    return "key", lit.constant(k)
end

function tab.seed(k)
    local out, slots = {}, {}
    if not k then return out, slots end
    if k.__type == "Table" then
        for _, x in ipairs(k.Value or {}) do
            local kind, name = key(x)
            local e = { kind = kind, key = name, pending = true }
            out[#out + 1] = e
            if kind == "field" then slots[name] = e end
        end
    elseif k.__type == "TableWithConstants" then
        for _, pair in ipairs(k.Value or {}) do
            local kind, name = key(pair.Key)
            local e = { kind = kind, key = name, pending = pair.Value == nil }
            if pair.Value ~= nil then e.val = ex.atom(lit.constant(pair.Value), true) end
            out[#out + 1] = e
            if kind == "field" then slots[name] = e end
        end
    end
    return out, slots
end

function tab.put(t, kind, name, val)
    local e = kind == "field" and t.slots and t.slots[name] or nil
    if e and e.pending then
        e.val = val
        e.pending = false
        return true
    end
    t.entries[#t.entries + 1] = { kind = kind, key = name, val = val }
    return true
end

function tab.mut(st, use, r)
    if not use or not use.pc then return false end
    local op = st.proto.Instructions[use.pc]
    local name = op and ins.name(op)
    if name == "SETTABLE" or name == "SETTABLEKS" or name == "SETUDATAKS" or name == "SETTABLEN" then
        return op.B == r
    elseif name == "SETLIST" then
        return op.A == r
    end
    return false
end

function tab.expr(t)
    local out = {}
    for _, e in ipairs(t.entries) do
        if not e.pending and e.val then
            if e.kind == "list" then
                out[#out + 1] = ex.str(e.val)
            elseif e.kind == "field" then
                out[#out + 1] = e.key .. " = " .. ex.str(e.val)
            else
                out[#out + 1] = "[" .. e.key .. "] = " .. ex.str(e.val)
            end
        end
    end
    return ex.atom(#out == 0 and "{}" or ("{ " .. table.concat(out, ", ") .. " }"), false)
end

function tab.use(st, v, r, pc)
    local t = st.tbl[v]
    if not t or t.done then return nil end
    t.done = true
    local node = tab.expr(t)
    if t.real <= 1 then return node end
    local name = st:useName(pc, r, nil)
    local depth = st.declared[name]
    if depth ~= nil and depth <= st.indent then
        st:out(name .. " = " .. ex.str(node))
    else
        st.declared[name] = st.indent
        st:out("local " .. name .. " = " .. ex.str(node))
    end
    return ex.atom(name, false)
end

return tab
]===],
    ["main.runtime.bytecode"] = [===[
local bc = {}

function bc.fromScript(obj)
    assert(typeof(obj) == "Instance", "LumenDecomp: target must be a Roblox Instance")
    assert(type(getscriptbytecode) == "function",
        "LumenDecomp: executor does not expose getscriptbytecode()")

    local ok, raw = pcall(getscriptbytecode, obj)
    if not ok then
        error("LumenDecomp: getscriptbytecode failed: " .. tostring(raw), 2)
    end

    local ty = typeof(raw)
    assert(type(raw) == "string" or ty == "buffer",
        "LumenDecomp: getscriptbytecode returned unsupported type " .. tostring(ty))

    return raw
end

return bc
]===],
    ["main.runtime.environment"] = [===[
local env = {}

function env.get()
    if type(getgenv) == "function" then
        local ok, e = pcall(getgenv)
        if ok and type(e) == "table" then
            return e
        end
    end

    if type(getfenv) == "function" then
        local ok, e = pcall(getfenv, 0)
        if ok and type(e) == "table" then
            return e
        end
    end

    return _G
end

function env.request()
    local e = env.get()

    return rawget(e, "request")
        or rawget(e, "http_request")
        or (type(syn) == "table" and syn.request)
end

return env
]===],
    ["main.runtime.http"] = [===[
local env = require("main.runtime.environment")

local http = {}

function http.get(url)
    local ok, body = pcall(function()
        return game:HttpGet(url)
    end)

    if ok and type(body) == "string" and #body > 0 then
        return body
    end

    local req = env.request()
    if type(req) == "function" then
        local rok, res = pcall(req, {
            Url = url,
            Method = "GET",
        })

        if rok and type(res) == "table" then
            local body = res.Body or res.body
            local code = res.StatusCode or res.Status or res.code

            if type(body) == "string"
                and #body > 0
                and (code == nil or (code >= 200 and code < 300)) then
                return body
            end
        end
    end

    error("LumenDecomp: HTTP GET failed for " .. tostring(url), 2)
end

return http
]===],
    ["main.runtime.iridium"] = [===[
local env = require("main.runtime.environment")
local http = require("main.runtime.http")
local patch = require("main.runtime.iridium_patch")

local iri = {}

local owner = "ActualMasterOogway"
local repo = "Iridium"
local commit = "2a834af6c6f72918a9222eb4ac6b258e4c6cd4bf"
local rawBase = "https://raw.githubusercontent.com/" .. owner .. "/" .. repo .. "/" .. commit .. "/"

local cache = {}
local NIL = {}
local LOADING = {}
local root = nil

local function resolve(name)
    if name == "@root" then
        return "Src/init.luau"
    end

    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end

    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local req

req = function(name)
    local path = resolve(name)
    local hit = cache[path]

    if hit == LOADING then
        error("LumenDecomp: cyclic Iridium dependency at " .. path, 2)
    elseif hit ~= nil then
        return hit == NIL and nil or hit
    end

    cache[path] = LOADING

    local ok, value = pcall(function()
        local src = http.get(rawBase .. path)
        src = patch.apply(path, src)
        src = "local require = __LUMEN_IRIDIUM_REQUIRE\n" .. src

        local chunk, err = loadstring(src, "@Iridium/" .. path)
        if not chunk then
            error("LumenDecomp: failed compiling Iridium/" .. path .. ": " .. tostring(err), 0)
        end

        return chunk()
    end)

    if not ok then
        cache[path] = nil
        error("LumenDecomp: failed loading Iridium/" .. path .. ": " .. tostring(value), 2)
    end

    cache[path] = value == nil and NIL or value
    return value
end

function iri.get()
    if root then
        return root
    end

    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local e = env.get()
    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)

    e[key] = req
    local ok, value = pcall(req, "@root")

    if old == nil then
        e[key] = nil
    else
        e[key] = old
    end

    if not ok then
        error(value, 2)
    end

    assert(type(value) == "table" and type(value.Deserialize) == "function",
        "LumenDecomp: Iridium root did not expose Deserialize")

    root = value
    return root
end

function iri.info()
    local pi = patch.info()
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
    }
end

return iri
]===],
    ["main.runtime.iridium_patch"] = [===[
local patch = {}

local rev = "v13-3"

local function rep(s, a, b, tag)
    local p = s:find(a, 1, true)
    if not p then error("LumenDecomp: Iridium patch mismatch: " .. tag, 3) end
    return s:sub(1, p - 1) .. b .. s:sub(p + #a)
end

function patch.apply(path, src)
    src = src:gsub("\r\n", "\n"):gsub("\r", "\n")
    if path == "Src/Luau/Spec.luau" then
        src = rep(src, "LBC_VERSION_MAX = 11", "LBC_VERSION_MAX = 13", "spec.max")
        src = rep(src, "LBC_VERSION_TARGET = 6", "LBC_VERSION_TARGET = 9", "spec.target")
        src = rep(src, "    LBC_VERSION_TARGET = 9,\n", "    LBC_VERSION_TARGET = 9,\n    LBC_VERSION_CLASSES = 100,\n", "spec.classes")
        src = rep(src, "    LBC_CONSTANT_CLASS_SHAPE = 10,\n", "    LBC_CONSTANT_CLASS_SHAPE = 10,\n    LBC_CONSTANT_VECTORD = 11,\n", "spec.vectord")
        src = rep(src, [[    LOP__COUNT = { Index = 88, Name = "_COUNT", HasAux = false },]], [[    LOP_CMPPROTO = { Index = 88, Name = "CMPPROTO", HasAux = true },
    LOP_NEWCLASS = { Index = 89, Name = "NEWCLASS", HasAux = true },
    LOP__COUNT = { Index = 90, Name = "_COUNT", HasAux = false },]], "spec.v12ops")
        return src
    end

    if path == "Src/init.luau" then
        src = rep(src, [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX}, got {self.BytecodeVersion})`)
    end]], [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and self.BytecodeVersion ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX} or classes, got {self.BytecodeVersion})`)
    end]], "init.classes")

        src = rep(src, [[    for i = 1, self.ProtoCount do
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
    end]], [[    self.ProtoSizes = {}
    for i = 1, self.ProtoCount do
        local ProtoSize = nil
        local ProtoStart = nil
        if self.BytecodeVersion >= 12 then
            ProtoSize = Bytecode:ReadVarInt()
            ProtoStart = Bytecode.Offset
            self.ProtoSizes[i] = ProtoSize
        end
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
        if ProtoSize then
            local ProtoEnd = ProtoStart + ProtoSize
            if Bytecode.Offset < ProtoEnd then
                Bytecode:seek(ProtoEnd - Bytecode.Offset)
            elseif Bytecode.Offset > ProtoEnd then
                error(`Proto {i} overread ({Bytecode.Offset - ProtoEnd} bytes)`)
            end
        end
    end]], "init.sizes")

        src = rep(src, [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    if Version >= 12 then
        local ProtoSize = Bytecode:ReadVarInt()
        Bytecode:seek(ProtoSize)
        return
    end

    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], "init.skiphead")

        src = rep(src, [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        end]], [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        elseif Kind == 11 then
            Bytecode:seek(32)
        end]], "init.vectord")



        src = rep(src, [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
            return nil
        end]], [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and Version ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
            return nil
        end]], "init.probeclasses")

        src = rep(src, [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        Bytecode:seek(4)]], [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        if Version >= 12 then
            Bytecode:ReadVarInt()
        end

        Bytecode:seek(4)]], "init.probe")
        return src
    end

    if path == "Src/Classes/Proto.luau" then
        src = rep(src, [[        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], [[        elseif ConstantType == LuauSpec.LuauBytecodeConstants.LBC_CONSTANT_VECTORD then
            local x, y, z, w =
                Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64()
            self.Constants[ConstantIndex] = Vector.new(x, y, z, w)
        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], "proto.vectord")

        local cost = [[    if Deserializer.BytecodeVersion >= 12 and bit32.band(self.Flags or 0, 8) ~= 0 then
        self.Cost = Bytecode:ReadVarInt64()
    end
]]
        local mark = "\n\treturn self\nend\n\nexport type Proto"
        local pos = src:find(mark, 1, true)
        if not pos then
            mark = "\n    return self\nend\n\nexport type Proto"
            pos = src:find(mark, 1, true)
        end
        if not pos then error("LumenDecomp: Iridium patch mismatch: proto.cost", 3) end
        src = src:sub(1, pos) .. cost .. src:sub(pos + 1)
        return src
    end

    return src
end

function patch.info()
    return { rev = rev, max = 13, target = 9, classes = 100 }
end

return patch
]===],
    ["main.worker"] = [===[
local cfg = require("main.config")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:decompile(obj, opt)
    opt = cfg(opt)
    local raw = bc.fromScript(obj)
    local parsed = iri.get():Deserialize(raw, opt.iridium)
    local src = decomp.new(opt):decompileParsed(parsed)
    return src
end

return worker
]===],
}

local cache = {}
local nilv = {}
local busy = {}

local function req(name)
    local hit = cache[name]
    if hit == busy then
        error("LumenDecomp: cyclic module " .. tostring(name), 2)
    elseif hit ~= nil then
        return hit == nilv and nil or hit
    end
    local src = assert(mod[name], "LumenDecomp: missing module " .. tostring(name))
    cache[name] = busy
    local fn, err = loadstring("return function(require)\n" .. src .. "\nend", "@Lumen/" .. name)
    assert(fn, err)
    local out = fn()(req)
    cache[name] = out == nil and nilv or out
    return out
end

return req("main.worker")
]=====]
function api:_workerSource() return workersrc end
local boot = {
    Binary = rawget(_G, "Binary"),
    Decompile = rawget(_G, "Decompile"),
    Tree = rawget(_G, "Tree"),
    IgnoreCoreScripts = rawget(_G, "IgnoreCoreScripts"),
    Parallel = rawget(_G, "Parallel"),
    MaxWorkers = rawget(_G, "MaxWorkers"),
}
if type(getgenv) == "function" then
    local ok, e = pcall(getgenv)
    if ok and type(e) == "table" then
        for _, k in ipairs({ "Binary", "Decompile", "Tree", "IgnoreCoreScripts", "Parallel", "MaxWorkers" }) do
            if boot[k] == nil then boot[k] = rawget(e, k) end
        end
    end
end
api:auto(boot)
return api
