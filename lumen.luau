assert(type(loadstring) == "function", "LumenDecomp requires loadstring()")

local mod = {
    ["main.analysis.dominators"] = [===[
local dom = {}

local function equal(a, b)
    for key in pairs(a) do if not b[key] then return false end end
    for key in pairs(b) do if not a[key] then return false end end
    return true
end

function dom.compute(blocks, check)
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
        if check then check() end
        chg = false

        for _, block in ipairs(blocks) do
            if check then check() end
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
    ["main.analysis.graph"] = [===[local ins = require("main.bytecode.instructions")
local regs = require("main.analysis.registers")
local dom = require("main.analysis.dominators")
local loops = require("main.analysis.loops")
local post = require("main.analysis.postdom")

local graph = {}

local function immediatefromsets(blocks, sets, check)
    local out = {}
    for _, b in ipairs(blocks) do
        if check then check() end
        local cand = {}
        for id in pairs(sets[b.id] or {}) do if id ~= b.id then cand[#cand + 1] = id end end
        table.sort(cand)
        for _, id in ipairs(cand) do
            local immediate = true
            for _, other in ipairs(cand) do
                if other ~= id and sets[other] and sets[other][id] then immediate = false break end
            end
            if immediate then out[b.id] = id break end
        end
    end
    return out
end

local function dominancefrontiers(blocks, idom, check)
    local df = {}; for _, b in ipairs(blocks) do df[b.id] = {} end
    for _, b in ipairs(blocks) do
        if check then check() end
        if #b.predecessors >= 2 then
            for _, pred in ipairs(b.predecessors) do
                local runner = pred
                local guard = {}
                while runner and runner ~= idom[b.id] and not guard[runner] do
                    guard[runner] = true
                    df[runner][b.id] = true
                    runner = idom[runner]
                end
            end
        end
    end
    return df
end

local function tarjan(blocks, check)
    local index, stack, onstack, idx, low, out = 0, {}, {}, {}, {}, {}
    local function visit(v)
        if check then check() end
        index += 1; idx[v] = index; low[v] = index; stack[#stack + 1] = v; onstack[v] = true
        for _, w in ipairs(blocks[v].successors) do
            if not idx[w] then visit(w); low[v] = math.min(low[v], low[w])
            elseif onstack[w] then low[v] = math.min(low[v], idx[w]) end
        end
        if low[v] == idx[v] then
            local nodes, set = {}, {}
            while true do
                local w = stack[#stack]; stack[#stack] = nil; onstack[w] = nil
                nodes[#nodes + 1] = w; set[w] = true
                if w == v then break end
            end
            table.sort(nodes)
            local cyclic = #nodes > 1
            if #nodes == 1 then for _, w in ipairs(blocks[nodes[1]].successors) do if w == nodes[1] then cyclic = true break end end end
            local entries, exits = {}, {}
            for _, n in ipairs(nodes) do
                for _, pred in ipairs(blocks[n].predecessors) do if not set[pred] then entries[n] = true end end
                for _, succ in ipairs(blocks[n].successors) do if not set[succ] then exits[succ] = true end end
            end
            local entrycount = 0; for _ in pairs(entries) do entrycount += 1 end
            out[#out + 1] = { nodes = nodes, set = set, cyclic = cyclic, entries = entries, exits = exits, irreducible = cyclic and entrycount > 1 }
        end
    end
    for _, b in ipairs(blocks) do if not idx[b.id] then visit(b.id) end end
    table.sort(out, function(a,b) return a.nodes[1] < b.nodes[1] end)
    return out
end

local function loopforest(natural, check)
    local parent = {}
    local function subset(a, b)
        for id in pairs(a) do if not b[id] then return false end end
        return true
    end
    for i, loop in ipairs(natural) do
        if check then check() end
        local best, bestsize
        local size = 0; for _ in pairs(loop.nodes) do size += 1 end
        for j, outer in ipairs(natural) do
            if i ~= j and subset(loop.nodes, outer.nodes) then
                local os = 0; for _ in pairs(outer.nodes) do os += 1 end
                if os > size and (not bestsize or os < bestsize) then best, bestsize = j, os end
            end
        end
        parent[i] = best
    end
    return parent
end

local function push(t, v)
    for _, x in ipairs(t) do if x == v then return end end
    t[#t + 1] = v
end

local function edgesuccessors(proto, pc, aux)
    local op = proto.Instructions[pc]
    local name = ins.name(op)
    local nx = ins.next(proto, pc, aux)
    local out = {}

    local function valid(p)
        return p >= 1 and p <= #proto.Instructions and not aux[p]
    end
    local function add(p)
        if valid(p) then push(out, p) end
    end

    if name == "RETURN" then
        return out
    elseif name == "LOADB" and (op.C or 0) ~= 0 then
        add(pc + (op.C or 0) + 1)
    elseif name == "FORNPREP" then

        add(nx)
        add(ins.jumpTarget(pc, op))
    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then

        add(ins.jumpTarget(pc, op))
    elseif ins.isConditional(op) then
        add(ins.jumpTarget(pc, op))
        add(nx)
    elseif ins.isUnconditional(op) then
        add(ins.jumpTarget(pc, op))
    else
        add(nx)
    end
    return out
end

local function verify(proto, aux, blocks, blockmap, nexts)
    local covered = {}
    for _, b in ipairs(blocks) do
        assert(b.id >= 1 and b.id <= #blocks, "LumenV4: CFG block id out of range")
        assert(#b.pcs > 0, "LumenV4: empty CFG block")
        for _, pc in ipairs(b.pcs) do
            assert(not aux[pc], "LumenV4: AUX word entered a basic block")
            assert(not covered[pc], "LumenV4: duplicate CFG PC " .. tostring(pc))
            covered[pc] = b.id
            assert(blockmap[pc] == b.id, "LumenV4: blockmap mismatch at PC " .. tostring(pc))
        end
        for _, sid in ipairs(b.successors) do
            assert(blocks[sid], "LumenV4: invalid CFG successor " .. tostring(sid))
            local back = false
            for _, pid in ipairs(blocks[sid].predecessors) do if pid == b.id then back = true break end end
            assert(back, "LumenV4: asymmetric CFG edge")
        end
    end
    for pc = 1, #proto.Instructions do
        if not aux[pc] and blockmap[pc] then
            for _, target in ipairs(nexts[pc] or {}) do
                assert(blockmap[target], "LumenV4: successor has no block at PC " .. tostring(target))
            end
        end
    end
    return true
end

function graph.build(proto, check, limits)
    local ops = proto.Instructions
    limits = limits or {}
    local maxinstructions = tonumber(limits.maxinstructions) or 0
    local maxblocks = tonumber(limits.maxblocks) or 0
    if maxinstructions > 0 and #ops > maxinstructions then
        error("LumenV4: STRUCTURED_COMPLEXITY proto instructions " .. tostring(#ops) .. " > " .. tostring(maxinstructions), 2)
    end
    if check then check() end
    local aux = ins.auxSlots(proto)
    local leaders = { [1] = true }
    local nexts = {}

    local function valid(pc)
        return pc >= 1 and pc <= #ops and not aux[pc]
    end

    for pc = 1, #ops do
        if not aux[pc] then
            local successors = edgesuccessors(proto, pc, aux)
            nexts[pc] = successors
            for _, target in ipairs(successors) do leaders[target] = true end

            local op = ops[pc]
            local name = ins.name(op)
            local nx = ins.next(proto, pc, aux)

            if name == "RETURN" or name == "LOADB" and (op.C or 0) ~= 0
                or name == "FORNPREP" or ins.isConditional(op) or ins.isUnconditional(op) then
                if valid(nx) then leaders[nx] = true end
            end
        end
    end

    local list = {}
    for pc in pairs(leaders) do if valid(pc) then list[#list + 1] = pc end end
    table.sort(list)

    local rawblocks, rawmap = {}, {}
    for index, startpc in ipairs(list) do
        local nextleader = list[index + 1] or (#ops + 1)
        local pcs = {}
        for pc = startpc, nextleader - 1 do
            if not aux[pc] then
                pcs[#pcs + 1] = pc
                rawmap[pc] = index
            end
        end
        if #pcs > 0 then
            rawblocks[index] = { id = index, startPC = startpc, endPC = pcs[#pcs], pcs = pcs, successors = {}, predecessors = {} }
        end
    end

    for _, b in ipairs(rawblocks) do
        for _, target in ipairs(nexts[b.endPC] or {}) do
            local sid = rawmap[target]
            if sid then push(b.successors, sid) end
        end
    end


    local reachable, todo = {}, { rawmap[1] }
    local at = 1
    while at <= #todo do
        local id = todo[at]; at += 1
        if id and not reachable[id] then
            reachable[id] = true
            for _, sid in ipairs(rawblocks[id].successors) do todo[#todo + 1] = sid end
        end
    end

    local remap, blocks = {}, {}
    for oldid, b in ipairs(rawblocks) do
        if reachable[oldid] then
            local id = #blocks + 1
            remap[oldid] = id
            blocks[id] = { id = id, startPC = b.startPC, endPC = b.endPC, pcs = b.pcs, successors = {}, predecessors = {} }
        end
    end

    local blockmap = {}
    for oldid, newid in pairs(remap) do
        local old = rawblocks[oldid]
        local b = blocks[newid]
        for _, pc in ipairs(b.pcs) do blockmap[pc] = newid end
        for _, oldsucc in ipairs(old.successors) do
            local sid = remap[oldsucc]
            if sid then push(b.successors, sid) end
        end
    end
    for _, b in ipairs(blocks) do
        for _, sid in ipairs(b.successors) do push(blocks[sid].predecessors, b.id) end
    end

    if maxblocks > 0 and #blocks > maxblocks then
        error("LumenV4: STRUCTURED_COMPLEXITY cfg blocks " .. tostring(#blocks) .. " > " .. tostring(maxblocks), 2)
    end
    if check then check() end
    local dominators = dom.compute(blocks, check)
    local idom = immediatefromsets(blocks, dominators, check)
    local postdom, ipdom, exitid = post.run(blocks, check)
    local naturalloops = loops.find(blocks, dominators, check)
    local sccs = tarjan(blocks, check)
    local out = {
        proto = proto,
        aux = aux,
        blocks = blocks,
        blockmap = blockmap,
        nexts = nexts,
        dominators = dominators,
        idom = idom,
        dominanceFrontiers = dominancefrontiers(blocks, idom, check),
        postdom = postdom,
        ipdom = ipdom,
        exitId = exitid,
        loops = naturalloops,
        loopForest = loopforest(naturalloops, check),
        sccs = sccs,
        irreducible = false,
        registerStats = regs.stats(proto, aux),
    }
    for _, component in ipairs(sccs) do if component.irreducible then out.irreducible = true break end end
    out.verified = verify(proto, aux, blocks, blockmap, nexts)
    return out
end

return graph
]===],
    ["main.analysis.loops"] = [===[
local loops = {}

function loops.find(blocks, dom, check)
    local out = {}

    for _, latch in ipairs(blocks) do
        if check then check() end
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

local function clone(s)
    local out = {}
    for k in pairs(s) do out[k] = true end
    return out
end

local function same(a, b)
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end

local function intersectinto(dst, src)
    for k in pairs(dst) do
        if not src[k] then dst[k] = nil end
    end
end

function post.run(blocks, check)
    local exitid = #blocks + 1
    local all = { [exitid] = true }
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = { [exitid] = { [exitid] = true } }
    for _, b in ipairs(blocks) do pd[b.id] = clone(all) end

    local dirty = true
    local iterations = 0
    local limit = math.max(64, (#blocks + 1) * (#blocks + 1) * 4)
    while dirty do
        if check then check() end
        iterations += 1
        if iterations > limit then
            error("LumenV4: post-dominator analysis failed to converge", 2)
        end
        dirty = false

        for i = #blocks, 1, -1 do
            local b = blocks[i]
            local succ = b.successors
            local set

            if #succ == 0 then
                set = clone(pd[exitid])
            else
                for _, sid in ipairs(succ) do
                    local src = assert(pd[sid], "LumenV4: invalid postdom successor " .. tostring(sid))
                    if not set then set = clone(src) else intersectinto(set, src) end
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

    local ip = {}
    for _, b in ipairs(blocks) do
        if check then check() end
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        table.sort(cand)

        for _, id in ipairs(cand) do
            local immediate = true

            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    immediate = false
                    break
                end
            end
            if immediate then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip, exitid
end

return post
]===],
    ["main.analysis.registers"] = [===[local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then set[value] = true end
end
local function range(set, first, last)
    for reg = first, math.min(last, 254) do add(set, reg) end
end


function regs.readWrite(op)
    local reads, writes, pack = {}, {}, {}
    local name = ins.name(op)
    local ra, rb, rc = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL" or name == "GETIMPORT"
        or name == "NEWTABLE" or name == "DUPTABLE" or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, ra)
    elseif name == "MOVE" then add(reads, rb); add(writes, ra)
    elseif name == "SETGLOBAL" or name == "SETUPVAL" then add(reads, ra)
    elseif name == "GETTABLE" then add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "SETTABLE" then add(reads, ra); add(reads, rb); add(reads, rc)
    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then add(reads, rb); add(writes, ra)
    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then add(reads, ra); add(reads, rb)
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then add(reads, rb); add(writes, ra); add(writes, ra + 1)
    elseif name == "CALL" or name == "CALLFB" then
        add(reads, ra)
        if rb == 0 then
            pack.openReadFrom = ra + 1
            pack.consumesTop = true
        elseif rb > 1 then range(reads, ra + 1, ra + rb - 1) end
        if rc == 0 then
            add(writes, ra)
            pack.openWriteFrom = ra
            pack.producesTop = true
        elseif rc > 1 then range(writes, ra, ra + rc - 2) end
    elseif name == "RETURN" then
        if rb == 0 then add(reads, ra); pack.openReadFrom = ra; pack.consumesTop = true
        elseif rb > 1 then range(reads, ra, ra + rb - 2) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        add(reads, rb); add(writes, ra)
    elseif name == "SUBRK" or name == "DIVRK" then add(reads, rc); add(writes, ra)
    elseif name == "CONCAT" then range(reads, rb, rc); add(writes, ra)
    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then add(reads, rb); add(writes, ra)
    elseif name == "SETLIST" then
        add(reads, ra)
        if rc == 0 then add(reads, rb); pack.openReadFrom = rb; pack.consumesTop = true
        elseif rc > 1 then range(reads, rb, rb + rc - 2) end
    elseif name == "FORNPREP" then
        range(reads, ra, ra + 2)


        range(writes, ra, ra + 2)
    elseif name == "FORNLOOP" then
        range(reads, ra, ra + 2); add(writes, ra + 2)
    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, ra, ra + 2); range(writes, ra, ra + 2)
    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, ra, ra + 2); add(writes, ra + 2)
        if count > 0 then range(writes, ra + 3, ra + 2 + count) end
    elseif name == "GETVARARGS" then
        if rb == 0 then add(writes, ra); pack.openWriteFrom = ra; pack.producesTop = true
        elseif rb > 1 then range(writes, ra, ra + rb - 2) end
    elseif name == "CAPTURE" then if ra == 0 or ra == 1 then add(reads, rb) end
    elseif name == "JUMPIF" or name == "JUMPIFNOT" or name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" or name == "CMPPROTO" then
        add(reads, ra)
    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, ra); add(reads, bit32.band(aux, 0xff))
    elseif name == "NEWCLASSMEMBER" then add(reads, ra); add(reads, rc)
    elseif name == "NEWCLASS" then if rb ~= 0xff then add(reads, rb) end; add(writes, ra)
    end

    return reads, writes, pack
end

function regs.stats(proto, aux)
    local stats = {}
    aux = aux or ins.auxSlots(proto)
    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = { reads = 0, writes = 0, firstWrite = nil, lastWrite = nil, firstRead = nil, lastRead = nil, firstAccess = nil, lastAccess = nil }
            stats[reg] = entry
        end
        return entry
    end
    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local reads, writes = regs.readWrite(proto.Instructions[pc])
            for reg in pairs(reads) do
                local e = get(reg); e.reads += 1; e.firstRead = e.firstRead or pc; e.lastRead = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
            end
            local name = ins.name(proto.Instructions[pc])
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local e = get(reg); e.writes += 1; e.firstWrite = e.firstWrite or pc; e.lastWrite = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
                end
            end
        end
    end
    return stats
end

return regs
]===],
    ["main.analysis.ssa"] = [===[local graph = require("main.analysis.graph")
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
]===],
    ["main.api"] = [===[
local ver = require("main.version")
local cfg = require("main.config")
local options = require("main.options")
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

api.DecompilerOptions = { new = options.new }

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

function api:tryDecompileBytecode(raw, opt)
    local ok, source, metadata = pcall(function()
        local text, meta = self:decompileBytecode(raw, opt)
        return text, meta
    end)

    if ok then
        return { success = true, source = source, metadata = metadata }
    end

    return { success = false, error = tostring(source) }
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

function api:warm()
    local ok, err = iri.warm()
    if not ok then error("LumenDecomp: Iridium warmup failed: " .. tostring(err), 2) end
    return true
end

function api:_iridiumPack()
    return iri.pack()
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
    ["main.ast.doblocks"] = [===[
local pass = {}

local function words(s, out)
    if type(s) ~= "string" then return end
    for x in s:gmatch("[%a_][%w_]*") do out[x] = true end
end

local function declraw(s)
    if type(s) ~= "string" then return {} end
    local head = s:match("^local%s+(.+)$")
    if not head or head:match("^function%s") then return {} end
    head = head:match("^(.-)%s*=") or head
    local out = {}
    for part in head:gmatch("[^,]+") do
        local name = part:match("^%s*([%a_][%w_]*)")
        if name then out[#out + 1] = name end
    end
    return out
end

local function decls(n)
    if n.kind == "raw" then return declraw(n.text) end
    if n.kind == "function" and n.localfn then return { n.name } end
    return {}
end

local function scanblock(b, out)
    for _, n in ipairs(b.body or {}) do
        if not n.dead then
            if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
                words(n.text, out)
            elseif n.kind == "if" then
                for _, x in ipairs(n.branches or {}) do
                    words(x.cond, out)
                    scanblock(x.body, out)
                end
                if n.elsebody then scanblock(n.elsebody, out) end
            elseif n.kind == "while" or n.kind == "repeat" then
                words(n.cond, out)
                scanblock(n.body, out)
            elseif n.kind == "for" then
                words(n.head, out)
                scanblock(n.body, out)
            elseif n.kind == "do" then
                scanblock(n.body, out)
            elseif n.kind == "callback" then
                words(n.pre, out)
                words(n.args, out)
                words(n.post, out)
                scanblock(n.body, out)
            elseif n.kind == "function" then
                words(n.name, out)
                words(n.args, out)
                scanblock(n.body, out)
            end
        end
    end
end

local function refs(n)
    local out = {}
    if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
        words(n.text, out)
    elseif n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do
            words(x.cond, out)
            scanblock(x.body, out)
        end
        if n.elsebody then scanblock(n.elsebody, out) end
    elseif n.kind == "while" or n.kind == "repeat" then
        words(n.cond, out)
        scanblock(n.body, out)
    elseif n.kind == "for" then
        words(n.head, out)
        scanblock(n.body, out)
    elseif n.kind == "do" then
        scanblock(n.body, out)
    elseif n.kind == "callback" then
        words(n.pre, out)
        words(n.args, out)
        words(n.post, out)
        scanblock(n.body, out)
    elseif n.kind == "function" then
        words(n.name, out)
        words(n.args, out)
        scanblock(n.body, out)
    end
    for _, name in ipairs(decls(n)) do out[name] = nil end
    return out
end

local function children(n, threshold)
    if n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do pass.run(x.body, threshold) end
        if n.elsebody then pass.run(n.elsebody, threshold) end
    elseif n.body then
        pass.run(n.body, threshold)
    end
end

function pass.run(block, threshold)
    threshold = math.floor(tonumber(threshold) or 0)
    for _, n in ipairs(block.body or {}) do children(n, threshold) end
    if threshold <= 0 or #(block.body or {}) < 2 then return block end

    local body = block.body
    local used = {}
    for i, n in ipairs(body) do used[i] = refs(n) end

    local last = {}
    for i = #body, 1, -1 do
        for name in pairs(used[i]) do
            if last[name] == nil then last[name] = i end
        end
    end

    local ranges = {}
    local start = nil
    local count = 0
    local finish = 0
    for i, n in ipairs(body) do
        local ds = decls(n)
        if #ds > 0 then
            if not start then start = i end
            count += #ds
            for _, name in ipairs(ds) do
                local x = last[name] or i
                if x > finish then finish = x end
            end
        end
        if start and i >= finish and count >= threshold then
            ranges[#ranges + 1] = { start, i }
            start = nil
            count = 0
            finish = 0
        end
    end

    if #ranges == 0 then return block end
    local by = {}
    for _, r in ipairs(ranges) do by[r[1]] = r[2] end
    local out = {}
    local i = 1
    while i <= #body do
        local e = by[i]
        if e then
            local sub = { kind = "block", body = {} }
            for j = i, e do sub.body[#sub.body + 1] = body[j] end
            out[#out + 1] = { kind = "do", body = sub }
            i = e + 1
        else
            out[#out + 1] = body[i]
            i += 1
        end
    end
    block.body = out
    return block
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


local pass = {}

function pass.run(root, opt)
    return root
end

return pass
]===],
    ["main.ast.printer"] = [===[
local printast = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hasname(node, name)
    if not node or node.dead then return false end
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local function hit(s) return type(s) == "string" and s:find(pat) ~= nil end
    if hit(node.text) or hit(node.cond) or hit(node.head) or hit(node.args) then return true end
    if node.kind == "if" then
        for _, b in ipairs(node.branches or {}) do
            if hit(b.cond) then return true end
            for _, x in ipairs(b.body.body or {}) do if hasname(x, name) then return true end end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body or {}) do if hasname(x, name) then return true end end end
    elseif node.body then
        for _, x in ipairs(node.body.body or {}) do if hasname(x, name) then return true end end
    end
    return false
end

local function recursive(node)
    for _, x in ipairs(node.body.body or {}) do if hasname(x, node.name) then return true end end
    return false
end

local function indent(opt, depth)
    local n = tonumber(opt.formatter and opt.formatter.IndentWidth) or 4
    n = math.max(0, math.min(16, math.floor(n)))
    return string.rep(" ", n * depth)
end

local function line(out, opt, depth, s, stmt)
    if stmt and opt.formatter and opt.formatter.AppendSemicolons then
        local last = s:sub(-1)
        if last ~= ";" and last ~= ":" then s = s .. ";" end
    end
    out[#out + 1] = indent(opt, depth) .. s
end

local function cond(opt, s)
    if opt.formatter and opt.formatter.ParenthesizeConditions then return "(" .. s .. ")" end
    return s
end

local function fnhead(node, opt)
    local args = node.args or ""
    if opt.functions == false then
        if node.localfn then return "local " .. node.name .. " = function(" .. args .. ")" end
        if node.assign then return node.name .. " = function(" .. args .. ")" end
        local base, field = node.name:match("^(.*):([%a_][%w_]*)$")
        if base and field then
            local a = args ~= "" and ("self, " .. args) or "self"
            return base .. "." .. field .. " = function(" .. a .. ")"
        end
        return node.name .. " = function(" .. args .. ")"
    end
    if node.localfn then return "local function " .. node.name .. "(" .. args .. ")" end
    if node.assign then return node.name .. " = function(" .. args .. ")" end
    return "function " .. node.name .. "(" .. args .. ")"
end

local function block(out, b, depth, opt)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, opt, depth, node.text, true)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, opt, depth, (i == 1 and "if " or "elseif ") .. cond(opt, branch.cond) .. " then")
                    block(out, branch.body, depth + 1, opt)
                end
                if node.elsebody then
                    line(out, opt, depth, "else")
                    block(out, node.elsebody, depth + 1, opt)
                end
                line(out, opt, depth, "end")
            elseif k == "while" then
                line(out, opt, depth, "while " .. cond(opt, node.cond) .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "repeat" then
                line(out, opt, depth, "repeat")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "until " .. cond(opt, node.cond))
            elseif k == "for" then
                line(out, opt, depth, node.head .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "do" then
                line(out, opt, depth, "do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "callback" then
                line(out, opt, depth, node.pre .. "function(" .. node.args .. ")")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end" .. node.post, true)
            elseif k == "function" then
                if opt.functions == false and node.localfn and recursive(node) then
                    line(out, opt, depth, "local " .. node.name, true)
                    line(out, opt, depth, node.name .. " = function(" .. (node.args or "") .. ")")
                else
                    line(out, opt, depth, fnhead(node, opt))
                end
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end", opt.functions == false or node.assign)
            end
        end
    end
end

function printast.run(root, opt)
    opt = opt or {}
    local out = {}
    block(out, root, 0, opt)
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
    guards = false,
    types = true,
    selects = false,
    returns = false,
    compound = false,
    inlineast = false,
    callbacks = false,
    booleans = false,
    smartnames = true,
    functions = true,
    doblocks = 0,
    iridium = nil,
    fidelity = true,
    structuredbudget = 1.25,
    structuredmaxinstructions = 8000,
    structuredmaxprotoinstructions = 4000,
    structuredmaxblocks = 256,
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
    FidelityMode = "fidelity",
    StructuredBudgetSeconds = "structuredbudget",
    StructuredMaxInstructions = "structuredmaxinstructions",
    StructuredMaxProtoInstructions = "structuredmaxprotoinstructions",
    StructuredMaxBlocks = "structuredmaxblocks",
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[map[k] or k] = v end end
    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    out.structuredbudget = math.max(0, tonumber(out.structuredbudget) or 1.25)
    out.structuredmaxinstructions = math.max(0, math.floor(tonumber(out.structuredmaxinstructions) or 8000))
    out.structuredmaxprotoinstructions = math.max(0, math.floor(tonumber(out.structuredmaxprotoinstructions) or 4000))
    out.structuredmaxblocks = math.max(0, math.floor(tonumber(out.structuredmaxblocks) or 256))
    if out.fidelity ~= false then

        out.fold = false
        out.guards = false
        out.selects = false
        out.returns = false
        out.compound = false
        out.inlineast = false
        out.callbacks = false
        out.booleans = false
        out.doblocks = 0
    end
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

    if self.opt.smartnames == false then
        if di then
            name = self.naming:nameAt(r, pc, nil)
        elseif src and src.kind == "param" then
            name = self.naming:unique("arg" .. tostring(src.reg + 1))
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
    ["main.decompiler.engine"] = [===[local irbuild = require("main.ir.build")
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
local lit = require("main.output.literals")
local regs = require("main.analysis.registers")
local vmfallback = (function()
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local vm = {}

local function line(out, depth, text)
    out[#out + 1] = string.rep("    ", depth) .. text
end

local function key2(proto, index)
    return proto.Constants and proto.Constants[(index or 0) + 1]
end

local function rawstr(constant)
    return lit.rawStringConstant(constant)
end

local function q(value)
    return lit.string(tostring(value or ""))
end

local function classshapeexpr(k)
    local name = rawstr(k and k.ClassName) or "AnonymousClass"
    local props, methods = {}, {}
    for _, v in ipairs(k and k.Properties or {}) do props[#props + 1] = q(rawstr(v) or "property") end
    for _, v in ipairs(k and k.Methods or {}) do methods[#methods + 1] = q(rawstr(v) or "method") end
    return "__classshape(" .. q(name) .. ", {" .. table.concat(props, ", ") .. "}, {" .. table.concat(methods, ", ") .. "})"
end

local function constexpr(proto, index)
    local k = key2(proto, index)
    if not k then return "nil" end
    if k.__type == "Import" then
        local parts = {}
        for _, part in ipairs(k.Value or {}) do parts[#parts + 1] = rawstr(part) or "?" end
        if #parts == 0 then return "nil" end
        local first = parts[1]
        local out
        if first == "type" and #parts == 1 then out = "__v4type"
        elseif first == "typeof" and #parts == 1 then out = "__v4typeof"
        elseif first == "class" then out = "__classlib"
        else out = "__env[" .. q(first) .. "]" end
        for i = 2, #parts do out = out .. "[" .. q(parts[i]) .. "]" end
        return out
    elseif k.__type == "ClassShape" then
        return classshapeexpr(k)
    elseif k.__type == "Closure" then
        return "nil"
    end
    return lit.constant(k)
end

local function aux(op)
    return op and op.AuxValue and op.AuxValue.Value or 0
end

local function methodkey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "unknownMethod"
end

local function tablekey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "?"
end

local function realpcs(proto)
    local slots = ins.auxSlots(proto)
    local pcs = {}
    for pc = 1, #proto.Instructions do
        if not slots[pc] then pcs[#pcs + 1] = pc end
    end
    return pcs, slots
end

local function argsexpr(first, count, openlast)
    if openlast then
        return "__unpack(" .. tostring(first) .. ", __top - 1)"
    end
    local args = {}
    for i = 0, count - 1 do args[#args + 1] = "__get(" .. tostring(first + i) .. ")" end
    return table.concat(args, ", ")
end

local function emitcallresult(out, depth, ra, rc, callexpr)
    if rc == 1 then
        line(out, depth, callexpr)
        line(out, depth, "__top = nil")
        return
    end

    line(out, depth, "local __ret = table.pack(" .. callexpr .. ")")
    if rc == 0 then
        line(out, depth, "for __i = 1, __ret.n do __set(" .. tostring(ra) .. " + __i - 1, __ret[__i]) end")
        line(out, depth, "__top = " .. tostring(ra) .. " + __ret.n")
    else
        local n = rc - 1
        for i = 0, n - 1 do line(out, depth, "__set(" .. tostring(ra + i) .. ", __ret[" .. tostring(i + 1) .. "])") end
        line(out, depth, "__top = nil")
    end
end

local function captureinfo(proto, startpc, child, slots)
    local list = {}
    local pc = startpc
    for i = 1, (child and child.UpvalueCount or 0) do
        while slots[pc] do pc += 1 end
        local op = proto.Instructions[pc]
        if not op or ins.name(op) ~= "CAPTURE" then

            list[i] = { kind = 0, src = nil, malformed = true }
        else
            list[i] = { kind = op.A or 0, src = op.B or 0, pc = pc }
            pc = ins.next(proto, pc, slots)
        end
    end
    return list, pc
end

local function emitcapturearray(out, depth, captures, selfreg)
    local selfvals = {}
    line(out, depth, "local __caps = {}")
    line(out, depth, "local __modes = {}")
    line(out, depth, "local __selfcaps = {}")
    for i, c in ipairs(captures) do
        if c.malformed then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 0 and c.src == selfreg then

            selfvals[#selfvals + 1] = i
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
            line(out, depth, "__selfcaps[" .. tostring(i) .. "] = true")
        elseif c.kind == 0 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = __get(" .. tostring(c.src) .. "), ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 1 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = __cell(" .. tostring(c.src) .. ")")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 1")
        else
            local ui = tostring((c.src or 0) + 1)
            line(out, depth, "local __u" .. tostring(i) .. " = __up[" .. ui .. "]")
            line(out, depth, "if __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".ref then __caps[" .. tostring(i) .. "] = __u" .. tostring(i) .. " else __caps[" .. tostring(i) .. "] = {v = __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".v or nil, ref = false} end")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 2")
        end
    end
    return selfvals
end

local function protomap(parsed)
    local byobject = {}
    for i, p in ipairs(parsed.Protos or {}) do byobject[p] = i end
    return byobject
end

local function closurechild(parsed, proto, op, byobject)
    local name = ins.name(op)
    if name == "NEWCLOSURE" then
        local child = proto.Protos and proto.Protos[(op.D or 0) + 1]
        return child, child and byobject[child] or nil
    elseif name == "DUPCLOSURE" then
        local k = key2(proto, op.D)
        if k and k.__type == "Closure" then
            local id = (k.Value or 0) + 1
            return parsed.Protos and parsed.Protos[id], id
        end
    end
end

local function emitprotofactory(out, parsed, proto, id, byobject, pulse)
    local pcs, slots = realpcs(proto)
    local maxstack = math.max(1, tonumber(proto.MaxStackSize) or 255)
    local params = math.max(0, tonumber(proto.ParameterCount) or 0)
    local pnames = {}
    for i = 0, params - 1 do pnames[#pnames + 1] = "__a" .. tostring(i) end
    if proto.IsVararg then pnames[#pnames + 1] = "..." end

    line(out, 0, "__factory[" .. tostring(id) .. "] = function(__up)")
    line(out, 1, "local function __fn(" .. table.concat(pnames, ", ") .. ")")
    line(out, 2, "local __r, __open = {}, {}")
    line(out, 2, "local __top = nil")
    if proto.IsVararg then line(out, 2, "local __var = table.pack(...)") else line(out, 2, "local __var = {n = 0}") end
    for i = 0, params - 1 do line(out, 2, "__r[" .. tostring(i) .. "] = __a" .. tostring(i)) end

    line(out, 2, "local function __get(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then return __c.v end")
    line(out, 3, "return __r[__i]")
    line(out, 2, "end")
    line(out, 2, "local function __set(__i, __v)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then __c.v = __v else __r[__i] = __v end")
    line(out, 2, "end")
    line(out, 2, "local function __cell(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c == nil then __c = {v = __r[__i], ref = true}; __open[__i] = __c end")
    line(out, 3, "return __c")
    line(out, 2, "end")
    line(out, 2, "local function __close(__a)")
    line(out, 3, "for __i = __a, " .. tostring(maxstack - 1) .. " do")
    line(out, 4, "local __c = __open[__i]")
    line(out, 4, "if __c ~= nil then __r[__i] = __c.v; __open[__i] = nil end")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 2, "local function __unpack(__first, __last)")
    line(out, 3, "if __last == nil or __last < __first then return end")
    line(out, 3, "local __n = __last - __first + 1")
    line(out, 3, "local __a = {n = __n}")
    line(out, 3, "for __i = 1, __n do __a[__i] = __get(__first + __i - 1) end")
    line(out, 3, "return table.unpack(__a, 1, __n)")
    line(out, 2, "end")

    local firstpc = pcs[1] or 1
    line(out, 2, "local __pc = " .. tostring(firstpc))
    line(out, 2, "while true do")

    local consumedcaptures = {}
    for _, pc in ipairs(pcs) do
        if pulse then pulse() end
        local op = proto.Instructions[pc]
        local name = ins.name(op)
        if name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = closurechild(parsed, proto, op, byobject)
            if child then
                local captures = captureinfo(proto, ins.next(proto, pc, slots), child, slots)
                for _, c in ipairs(captures) do if c.pc then consumedcaptures[c.pc] = true end end
            end
        end
    end

    local branchindex = 0
    for _, pc in ipairs(pcs) do
        if pulse then pulse() end
        if not consumedcaptures[pc] then
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local nextpc = ins.next(proto, pc, slots)
            branchindex += 1
            line(out, 3, (branchindex == 1 and "if " or "elseif ") .. "__pc == " .. tostring(pc) .. " then")
            local d = 4
            local ra, rb2, rc, rd = op.A or 0, op.B or 0, op.C or 0, op.D or 0
            local av = aux(op)

            if name == "NOP" or name == "BREAK" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name:match("^FASTCALL") then
                line(out, d, "__pc = " .. tostring(nextpc))
            elseif name == "LOADNIL" then
                line(out, d, "__set(" .. ra .. ", nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADB" then
                line(out, d, "__set(" .. ra .. ", " .. (rb2 == 1 and "true" or "false") .. ")")
                line(out, d, "__pc = " .. tostring(rc ~= 0 and (pc + rc + 1) or nextpc))
            elseif name == "LOADN" then
                line(out, d, "__set(" .. ra .. ", " .. lit.number(rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADKX" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, av) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MOVE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                local value = key == "type" and "__v4type" or (key == "typeof" and "__v4typeof" or (key == "class" and "__classlib" or ("__env[" .. q(key) .. "]")))
                line(out, d, "__set(" .. ra .. ", " .. value .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                line(out, d, "__env[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "__set(" .. ra .. ", __u and __u.v or nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "if __u == nil then __u = {v = nil, ref = true}; __up[" .. tostring(rb2 + 1) .. "] = __u end")
                line(out, d, "__u.v = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "CLOSEUPVALS" then
                line(out, d, "__close(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETIMPORT" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[__get(" .. rc .. ")])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLE" then
                line(out, d, "__get(" .. rb2 .. ")[__get(" .. rc .. ")] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
                local key = tablekey(proto, op, name == "GETUDATAKS")
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. q(key) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
                local key = tablekey(proto, op, name == "SETUDATAKS")
                line(out, d, "__get(" .. rb2 .. ")[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEN" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEN" then
                line(out, d, "__get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWTABLE" then
                line(out, d, "__set(" .. ra .. ", {})"); line(out, d, "__pc = " .. nextpc)
            elseif name == "DUPTABLE" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
                local child, childid = closurechild(parsed, proto, op, byobject)
                local captures, after = captureinfo(proto, nextpc, child, slots)
                local selfvals = emitcapturearray(out, d, captures, ra)
                if childid then
                    if name == "DUPCLOSURE" then
                        line(out, d, "local __cl = __dup(" .. q(tostring(id) .. ":" .. tostring(rd)) .. ", " .. tostring(childid) .. ", __caps, __modes, __selfcaps)")
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    else
                        line(out, d, "local __cl = __factory[" .. tostring(childid) .. "](__caps)")
                        for _, ci in ipairs(selfvals) do line(out, d, "__caps[" .. tostring(ci) .. "].v = __cl") end
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    end
                else
                    line(out, d, "__set(" .. ra .. ", function(...) return nil end)")
                end
                line(out, d, "__pc = " .. tostring(after))
            elseif name == "CAPTURE" then

                line(out, d, "__pc = " .. nextpc)
            elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
                local key = methodkey(proto, op, name == "NAMECALLUDATA")
                local callpc = nextpc
                local callop = proto.Instructions[callpc]
                local callname = callop and ins.name(callop) or ""
                if callop and (callname == "CALL" or callname == "CALLFB") and (callop.A or -1) == ra then
                    local cb, cc = callop.B or 0, callop.C or 0
                    local argtext
                    if cb == 0 then argtext = argsexpr(ra + 2, 0, true) else argtext = argsexpr(ra + 2, math.max(0, cb - 2), false) end
                    local callexpr
                    if lit.identifier(key) then
                        callexpr = "(__get(" .. rb2 .. ")):" .. key .. "(" .. argtext .. ")"
                    else
                        local pre = "(__get(" .. rb2 .. "))[" .. q(key) .. "]"
                        if argtext ~= "" then argtext = "__get(" .. rb2 .. "), " .. argtext else argtext = "__get(" .. rb2 .. ")" end
                        callexpr = "(" .. pre .. ")(" .. argtext .. ")"
                    end
                    emitcallresult(out, d, ra, cc, callexpr)
                    line(out, d, "__pc = " .. tostring(ins.next(proto, callpc, slots)))
                else
                    line(out, d, "local __obj = __get(" .. rb2 .. ")")
                    line(out, d, "__set(" .. ra .. ", __obj[" .. q(key) .. "])")
                    line(out, d, "__set(" .. tostring(ra + 1) .. ", __obj)")
                    line(out, d, "__pc = " .. nextpc)
                end
            elseif name == "CALL" or name == "CALLFB" then
                local argtext
                if rb2 == 0 then argtext = argsexpr(ra + 1, 0, true) else argtext = argsexpr(ra + 1, math.max(0, rb2 - 1), false) end
                emitcallresult(out, d, ra, rc, "(__get(" .. ra .. "))(" .. argtext .. ")")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "RETURN" then
                if rb2 == 1 then line(out, d, "return")
                elseif rb2 == 0 then line(out, d, "return __unpack(" .. ra .. ", (__top or " .. ra .. ") - 1)")
                else
                    local vals = {}
                    for r = ra, ra + rb2 - 2 do vals[#vals + 1] = "__get(" .. tostring(r) .. ")" end
                    line(out, d, "return " .. table.concat(vals, ", "))
                end
            elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "JUMPIF" or name == "JUMPIFNOT" then
                local test = name == "JUMPIF" and ("__get(" .. ra .. ")") or ("not __get(" .. ra .. ")")
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
                local rb = bit32.band(av, 0xff)
                local cmp = ({JUMPIFEQ = "==", JUMPIFNOTEQ = "~=", JUMPIFLT = "<", JUMPIFLE = "<=", JUMPIFNOTLT = "<", JUMPIFNOTLE = "<="})[name]
                local test = "__get(" .. ra .. ") " .. cmp .. " __get(" .. rb .. ")"
                if name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" then
                local rhs
                if name == "JUMPXEQKNIL" then rhs = "nil"
                elseif name == "JUMPXEQKB" then rhs = bit32.band(av, 1) == 1 and "true" or "false"
                else rhs = constexpr(proto, bit32.band(av, 0xffffff)) end
                local test = "__get(" .. ra .. ") == " .. rhs
                if bit32.btest(av, 0x80000000) then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
                local symbol = ({ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " __get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" then
                local symbol = ({ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " " .. constexpr(proto, rc) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SUBRK" or name == "DIVRK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rb2) .. (name == "SUBRK" and " - " or " / ") .. "__get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "AND" or name == "OR" then
                if name == "AND" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rc .. ")) else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", __get(" .. rc .. ")) end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "ANDK" or name == "ORK" then
                local kval = constexpr(proto, rc)
                if name == "ANDK" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", " .. kval .. ") else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", " .. kval .. ") end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CONCAT" then
                line(out, d, "local __x = __get(" .. rc .. ")")
                for r = rc - 1, rb2, -1 do line(out, d, "__x = __get(" .. r .. ") .. __x") end
                line(out, d, "__set(" .. ra .. ", __x)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NOT" then
                line(out, d, "__set(" .. ra .. ", not __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MINUS" then
                line(out, d, "__set(" .. ra .. ", -__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LENGTH" then
                line(out, d, "__set(" .. ra .. ", #__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETLIST" then
                line(out, d, "local __t = __get(" .. ra .. ")")
                if rc == 0 then
                    line(out, d, "local __n = (__top or " .. rb2 .. ") - " .. rb2)
                    line(out, d, "for __i = 0, __n - 1 do __t[" .. av .. " + __i] = __get(" .. rb2 .. " + __i) end")
                    line(out, d, "__top = nil")
                else
                    for i = 0, rc - 2 do line(out, d, "__t[" .. tostring(av + i) .. "] = __get(" .. tostring(rb2 + i) .. ")") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "FORNPREP" then
                line(out, d, "local __limit = __fornum(__get(" .. ra .. "))")
                line(out, d, "local __step = __fornum(__get(" .. tostring(ra + 1) .. "))")
                line(out, d, "local __idx = __fornum(__get(" .. tostring(ra + 2) .. "))")
                line(out, d, "__set(" .. ra .. ", __limit); __set(" .. tostring(ra + 1) .. ", __step); __set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. nextpc .. " else __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " end")
            elseif name == "FORNLOOP" then
                line(out, d, "local __limit, __step = __get(" .. ra .. "), __get(" .. tostring(ra + 1) .. ")")
                line(out, d, "local __idx = __get(" .. tostring(ra + 2) .. ") + __step")
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then

                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGPREP" then
                line(out, d, "local __g = __get(" .. ra .. ")")
                line(out, d, "if type(__g) ~= \"function\" then")
                line(out, d + 1, "local __ng, __ns, __ni = __iterprep(__g)")
                line(out, d + 1, "__set(" .. ra .. ", __ng); __set(" .. tostring(ra + 1) .. ", __ns); __set(" .. tostring(ra + 2) .. ", __ni)")
                line(out, d, "end")
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGLOOP" then
                local count = math.max(1, bit32.band(av, 0xff))
                line(out, d, "local __ret = table.pack((__get(" .. ra .. "))(__get(" .. tostring(ra + 1) .. "), __get(" .. tostring(ra + 2) .. ")))")
                for i = 1, count do line(out, d, "__set(" .. tostring(ra + 2 + i) .. ", __ret[" .. tostring(i) .. "])") end
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __ret[1])")
                line(out, d, "if __ret[1] ~= nil then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "GETVARARGS" then
                if rb2 == 0 then
                    line(out, d, "for __i = 1, __var.n do __set(" .. ra .. " + __i - 1, __var[__i]) end")
                    line(out, d, "__top = " .. ra .. " + __var.n")
                else
                    for i = 1, rb2 - 1 do line(out, d, "__set(" .. tostring(ra + i - 1) .. ", __var[" .. tostring(i) .. "])") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CMPPROTO" then


                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "NEWCLASS" then
                line(out, d, "local __super = " .. (rb2 ~= 0xff and ("__get(" .. rb2 .. ")") or "nil"))
                line(out, d, "__set(" .. ra .. ", __newclass(" .. constexpr(proto, av) .. ", __super))")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLASSMEMBER" then
                local key = rawstr(key2(proto, av)) or "member"
                line(out, d, "__classmember(__get(" .. ra .. "), " .. q(key) .. ", __get(" .. rc .. "))")
                line(out, d, "__pc = " .. nextpc)
            else

                line(out, d, "error(" .. q("LumenV4 VM fallback: unknown opcode " .. tostring(name) .. " at pc " .. tostring(pc)) .. ")")
            end
        end
    end

    line(out, 3, "else")
    line(out, 4, "error(\"LumenV4 VM fallback: invalid pc \" .. tostring(__pc))")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 1, "end")
    line(out, 1, "return __fn")
    line(out, 0, "end")
    line(out, 0, "")
end

function vm.run(parsed, reason)
    local entry = assert(parsed and parsed.Protos and parsed.Protos[parsed.ProtoEntryPoint], "LumenV4 VM fallback: missing entry proto")
    local slice = os.clock()
    local function pulse(force)
        local now = os.clock()
        if force or now - slice >= 0.008 then
            if task and type(task.wait) == "function" then task.wait() end
            slice = os.clock()
        end
    end
    local byobject = protomap(parsed)
    local decoded = 0
    for _, proto in ipairs(parsed.Protos or {}) do
        pulse()
        local pcs = realpcs(proto)
        decoded += #pcs
    end
    local bytecodeversion = tonumber(parsed.BytecodeVersion) or 0
    local header = ("-- LumenV4 status=VM_FALLBACK coverage=100.00 reachable=%d covered=%d blocks=%d structuredBlocks=0 fallbackBlocks=%d phis=0 undefs=0 packs=0 cells=0 objects=0 escapedObjects=0 irreducible=0 bytecodeVersion=%d ssa=false parser=true diagnostics=0")
        :format(decoded, decoded, decoded, decoded, bytecodeversion)
    local out = {
        header,
        "-- Structured recovery failed; this function is a direct decoded-bytecode state machine.",
        "-- Original recovery reason: " .. tostring(reason or "semantic fallback"):gsub("[\r\n]+", " "),
        "local __env = (getfenv and getfenv(0)) or _G",
        "local __factory = {}",
        "local __dupcache = {}",
        "",
        "local function __fornum(v)",
        "    if type(v) == \"number\" then return v end",
        "    local n = tonumber(v)",
        "    if n == nil then error(\"invalid 'for' limit/step/index (number expected)\", 2) end",
        "    return n",
        "end",
        "",
        "local function __mt(v)",
        "    if type(getrawmetatable) == \"function\" then",
        "        local ok, mt = pcall(getrawmetatable, v)",
        "        if ok and mt ~= nil then return mt end",
        "    end",
        "    return getmetatable(v)",
        "end",
        "",
        "local function __iterprep(v)",
        "    if type(v) == \"table\" then",
        "        local mt = __mt(v)",
        "        local it = mt and mt.__iter",
        "        if it ~= nil then",
        "            local g, s, i = it(v)",
        "            return g, s, i",
        "        end",
        "        if mt and mt.__call then return v, nil, nil end",
        "        return next, v, nil",
        "    end",
        "    local mt = __mt(v)",
        "    local it = mt and mt.__iter",
        "    if it ~= nil then return it(v) end",
        "    return v, nil, nil",
        "end",
        "",
        "local __realtype = type",
        "local __realtypeof = typeof or type",
        "local __classof = setmetatable({}, {__mode = \"k\"})",
        "local __classmeta = setmetatable({}, {__mode = \"k\"})",
        "local __isclass = setmetatable({}, {__mode = \"k\"})",
        "",
        "local function __classshape(name, props, methods)",
        "    return {__name = name, __props = props, __methods = methods}",
        "end",
        "",
        "local function __classlookup(cls, key)",
        "    local c = cls",
        "    while c do",
        "        local v = rawget(c, key)",
        "        if v ~= nil then return v end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return nil",
        "end",
        "",
        "local function __isinstance(obj, cls)",
        "    if not __isclass[cls] then return false end",
        "    local c = __classof[obj]",
        "    while c do",
        "        if c == cls then return true end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return false",
        "end",
        "",
        "local __classlib = setmetatable({",
        "    isinstance = __isinstance,",
        "    classof = function(v) return __classof[v] end,",
        "}, {__index = __env.class})",
        "",
        "local function __v4type(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtype(v)",
        "end",
        "local function __v4typeof(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtypeof(v)",
        "end",
        "",
        "local __classmetamethods = {",
        "    __add=true,__sub=true,__mul=true,__div=true,__idiv=true,__mod=true,__pow=true,",
        "    __unm=true,__len=true,__eq=true,__lt=true,__le=true,__concat=true,__tostring=true,",
        "    __iter=true,__call=true,",
        "}",
        "",
        "local function __classmember(cls, name, value)",
        "    rawset(cls, name, value)",
        "    local m = __classmeta[cls]",
        "    if m and __classmetamethods[name] then",
        "        m.instanceMt[name] = function(...) return value(...) end",
        "    end",
        "end",
        "",
        "local function __newclass(shape, super)",
        "    local cls = {}",
        "    local props, propset = {}, {}",
        "    if super and __classmeta[super] then",
        "        for _, p in ipairs(__classmeta[super].props) do props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    for _, p in ipairs(shape and shape.__props or {}) do",
        "        if not propset[p] then props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    local imt = {}",
        "    local meta = {shape = shape or {}, super = super, props = props, propset = propset, instanceMt = imt}",
        "    __classmeta[cls] = meta",
        "    __isclass[cls] = true",
        "    imt.__index = function(obj, key)",
        "        local v = __classlookup(cls, key)",
        "        if v ~= nil then return v end",
        "        if propset[key] then return nil end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    imt.__newindex = function(obj, key, value)",
        "        if propset[key] then rawset(obj, key, value); return end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    local cmt = {}",
        "    cmt.__index = function(_, key)",
        "        local v = super and __classlookup(super, key) or nil",
        "        if v ~= nil then return v end",
        "        error(\"this class does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    cmt.__newindex = function(_, key) error(\"attempt to index class with '\" .. tostring(key) .. \"'\", 2) end",
        "    cmt.__call = function(_, init)",
        "        local obj = {}",
        "        __classof[obj] = cls",
        "        setmetatable(obj, imt)",
        "        if init ~= nil then",
        "            for _, p in ipairs(props) do rawset(obj, p, init[p]) end",
        "        end",
        "        return obj",
        "    end",
        "    setmetatable(cls, cmt)",
        "    return cls",
        "end",
        "",
        "local function __samecaps(a, b, modes, selfcaps, fn)",
        "    if not a then return false end",
        "    for i = 1, #b do",
        "        if modes[i] == 0 then",
        "            local expected = selfcaps[i] and fn or (b[i] and b[i].v)",
        "            if not rawequal(a[i] and a[i].v, expected) then return false end",
        "        elseif modes[i] == 2 then",
        "            local ar, br = a[i] and a[i].ref, b[i] and b[i].ref",
        "            if ar or br then",
        "                if a[i] ~= b[i] then return false end",
        "            elseif not rawequal(a[i] and a[i].v, b[i] and b[i].v) then return false end",
        "        elseif a[i] ~= b[i] then return false end",
        "    end",
        "    return true",
        "end",
        "",
        "local function __dup(cacheKey, id, caps, modes, selfcaps)",
        "    local c = __dupcache[cacheKey]",
        "    if c ~= nil and __samecaps(c.caps, caps, modes, selfcaps, c.fn) then return c.fn end",
        "    local fn = __factory[id](caps)",
        "    for i in pairs(selfcaps) do caps[i].v = fn end",
        "    if c == nil then __dupcache[cacheKey] = {fn = fn, caps = caps, modes = modes} end",
        "    return fn",
        "end",
        "",
    }

    for i, proto in ipairs(parsed.Protos or {}) do pulse(); emitprotofactory(out, parsed, proto, i, byobject, pulse) end
    pulse(true)
    local entryid = byobject[entry] or parsed.ProtoEntryPoint
    line(out, 0, "return (__factory[" .. tostring(entryid) .. "]({}))()")

    local source = table.concat(out, "\n")
    if type(loadstring) == "function" then
        local fn, err = loadstring(source, "@LumenV4/vm-fallback-verify")
        if not fn then error("LumenV4 VM fallback generator emitted invalid Luau: " .. tostring(err), 2) end
    end
    return source, {
        status = "VM_FALLBACK",
        fallback = true,
        syntaxValid = true,
        originCoverageValid = true,
        coverage = 1,
        verification = "decoded-bytecode-total-dispatch",
        structuredError = tostring(reason or ""),
    }
end

return vm
end)()

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

local function hashard(st)

    return #st.bad > 0
end

function decomp.new(opt) return setmetatable({ opt = opt or {}, deadline = nil, slice = os.clock() }, decomp) end

function decomp:_check()
    local now = os.clock()
    if now - (self.slice or now) >= 0.008 then
        if task and type(task.wait) == "function" then task.wait() end
        self.slice = os.clock()
        now = self.slice
    end
    if self.deadline and now > self.deadline then
        error("LumenV4: STRUCTURED_BUDGET exceeded", 2)
    end
end

function decomp:_state(proto, up, ph)
    self:_check()
    local limits = {
        maxinstructions = self.opt.structuredmaxprotoinstructions or self.opt.structuredmaxinstructions,
        maxblocks = self.opt.structuredmaxblocks,
    }
    local ir = irbuild.run(proto, function() self:_check() end, limits)
    ir.paramhints = ph or {}
    self:_check()
    ir = irpass.run(ir, self.opt, function() self:_check() end)
    self:_check()
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    local st = context.new(proto, ir, naming, up, lower.new(), self.opt)
    st.v4 = { fallback = false, visited = {}, status = "STRUCTURED", cellNames = {} }


    if ir.cells and next(ir.cells) then
        local oldvname = st.vname
        local ids = {}
        for cid in pairs(ir.cells) do ids[#ids + 1] = cid end
        table.sort(ids)
        local resolvedcell = {}
        for raw, cid in pairs(ir.cellOfValue or {}) do
            local rv = ir:resolve(raw)
            if rv then resolvedcell[rv] = resolvedcell[rv] or cid end
        end
        for _, cid in ipairs(ids) do
            local cell = ir.cells[cid]
            local cp = cell.captures and cell.captures[1]
            local raw = cp and ir.ssa.usesByPC[cp] and ir.ssa.usesByPC[cp][cell.reg] or nil
            if raw then
                st.v4.cellNames[cid] = oldvname(st, raw, cell.reg, nil, cp)
            else
                st.v4.cellNames[cid] = naming:unique("cell" .. tostring(cid))
            end
        end
        st.vname = function(self, value, reg, hint, pc)
            local cid = value and ((self.ir.cellOfValue and self.ir.cellOfValue[value]) or resolvedcell[self.ir:resolve(value)])
            local cellname = cid and self.v4.cellNames[cid]
            if cellname then return cellname end
            return oldvname(self, value, reg, hint, pc)
        end
    end


    for bid, phis in pairs(ir.phis or {}) do
        local block = assert(ir.cfg.blocks[bid], "LumenV4: phi references invalid CFG block")
        for reg, phi in pairs(phis) do
            local pid = ir:resolve(phi.id)
            if pid and not ir.dead[pid] then
                local target = st:vname(pid, reg, nil, block.startPC)
                for pred, raw in pairs(phi.incoming or {}) do
                    local rid = ir:resolve(raw)
                    local value = rid and ir.vals[rid] or nil
                    if value and value.kind ~= "undef" then
                        local pb = assert(ir.cfg.blocks[pred], "LumenV4: phi references invalid predecessor")
                        local source = st:vname(rid, reg, nil, pb.endPC)
                        if source ~= target then
                            error(("LumenV4: UNSUPPORTED SSA destruction mismatch for phi v%d r%d: b%d uses %s, target is %s")
                                :format(pid, reg, pred, tostring(source), tostring(target)), 2)
                        end
                    end
                end
            end
        end
    end
    st.v4.ssaDestructionVerified = true
    return st
end

local function arguments(st, proto)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    return args
end

local function preparepacks(st)
    st.packnames = {}
    st.directPacks = {}
    st.directPackValues = {}

    local consumers = {}
    for pc, producer in pairs(st.ssa.packInput or {}) do
        if type(producer) == "number" then
            local list = consumers[producer]
            if not list then list = {}; consumers[producer] = list end
            list[#list + 1] = pc
        end
    end

    local pcs = {}
    for pc, pack in pairs(st.ssa.packsByPC or {}) do
        if pack and pack.producesTop then pcs[#pcs + 1] = pc end
    end
    table.sort(pcs)

    local names = {}
    for _, pc in ipairs(pcs) do
        local list = consumers[pc] or {}
        local consumer = #list == 1 and list[1] or nil
        local sameblock = consumer and st.cfg.blockmap[pc] == st.cfg.blockmap[consumer]
        if consumer and sameblock and st:next(pc) == consumer then


            st.directPacks[pc] = consumer
        else
            local name = st.naming:unique("__pack" .. tostring(pc))
            st.packnames[pc] = name
            st.declared[name] = 0
            names[#names + 1] = name
        end
    end

    for i = 1, #names, 8 do
        local chunk = {}
        for j = i, math.min(i + 7, #names) do chunk[#chunk + 1] = names[j] end
        st:out("local " .. table.concat(chunk, ", "))
    end
end

local function packtail(st, pc)
    local producer = st.ssa.packInput and st.ssa.packInput[pc] or nil
    if producer == st.ssa.ambiguousPack then
        error("LumenV4: UNSUPPORTED divergent ValuePack at pc " .. tostring(pc), 2)
    end
    if type(producer) ~= "number" then
        error("LumenV4: UNSUPPORTED open ValuePack consumer without unique producer at pc " .. tostring(pc), 2)
    end
    local _, _, pp = regs.readWrite(st.proto.Instructions[producer])
    local direct = st.directPackValues and st.directPackValues[producer]
    if direct then return producer, pp.openWriteFrom, direct.node end
    local name = assert(st.packnames and st.packnames[producer], "LumenV4: missing ValuePack temp")
    return producer, pp.openWriteFrom, ex.atom("table.unpack(" .. name .. ", 1, " .. name .. ".n)", false)
end

function decomp:_op(st, pc)
    local op = st.proto.Instructions[pc]
    local _, _, pack = regs.readWrite(op)
    st.top = nil
    if pack.consumesTop then
        local _, base, node = packtail(st, pc)
        if type(base) ~= "number" then error("LumenV4: invalid ValuePack producer at pc " .. tostring(pc), 2) end
        if pack.openReadFrom and base < pack.openReadFrom then
            error("LumenV4: invalid ValuePack base at pc " .. tostring(pc), 2)
        end
        st.top = { reg = base, node = node, v4 = true }
    end

    local name = ins.name(op)
    local nx

    if name == "NEWTABLE" then
        st:set(pc, op.A, ex.atom("{}", false))
        nx = st:next(pc)
    elseif name == "DUPTABLE" then
        local constant = st.proto.Constants and st.proto.Constants[(op.D or 0) + 1]
        st:set(pc, op.A, ex.atom(lit.constant(constant), false))
        nx = st:next(pc)
    else
        nx = ops.run(self, st, pc)
    end

    if pack.producesTop then
        local produced = st.top
        if not produced or not produced.node then
            error("LumenV4: open-result producer did not expose a ValuePack at pc " .. tostring(pc), 2)
        end
        local base = assert(pack.openWriteFrom, "LumenV4: ValuePack producer has no base")
        if st.directPacks and st.directPacks[pc] then
            st.directPackValues[pc] = { reg = base, node = produced.node }
        else
            local name = assert(st.packnames and st.packnames[pc], "LumenV4: missing producer ValuePack temp")
            st:out(name .. " = table.pack(" .. ex.str(produced.node) .. ")")
            for reg, version in pairs(st.ssa.defsByPC[pc] or {}) do
                if reg >= base then
                    local node = ex.atom(name .. "[" .. tostring(reg - base + 1) .. "]", false)
                    st.vals[version] = node
                    st.expr[version] = node
                end
            end
        end
        st.top = nil
    end
    return nx
end

function decomp:_child(proto, up, ph)
    self:_check()
    local st = self:_state(proto, up, ph)
    local args = arguments(st, proto)
    preparepacks(st)
    self:_region(st, 1, #proto.Instructions + 1, {})

    if hashard(st) then

        st = self:_state(proto, up, ph)
        args = arguments(st, proto)
        preparepacks(st)
        st.v4.fallback = true
        st.v4.status = "LOSSLESS_FALLBACK"
        self:_dispatcher(st)
        if hashard(st) then
            error("LumenV4: UNSUPPORTED semantic lowering issue: " .. table.concat(st.bad, " | "), 2)
        end
    end

    self:_check()
    local root = astpass.run(st.ast:done(), self.opt)
    self:_check()
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, a = info.loop, op.A


    local body = st:next(pc)
    local varreg = a + 2
    local bodystart = body
    local first = st.proto.Instructions[body]
    if first and ins.name(first) == "MOVE" and first.B == a + 2 and first.A == a + 3 then
        varreg = a + 3
        st.v4.visited[body] = true
        bodystart = st:next(body)
    end

    local old = st.alias[varreg]
    local lv = varreg == a + 2 and st:veruse(body, varreg) or st:verdef(body, varreg)
    if not lv then lv = st:veruse(loop, a + 2) or st:verdef(loop, a + 2) end
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, varreg, bodystart, loop) and "_" or st:vname(lv, varreg, fall, body)
    local limit, step, init = ex.str(st:loopx(pc, loop, a)), ex.str(st:loopx(pc, loop, a + 1)), ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head ..= ", " .. step end
    st:out(head .. " do"); st.indent += 1
    st.alias[varreg] = var; st.declared[var] = st.indent
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, bodystart, loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end"); st.alias[varreg] = old
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, lop = info.loop, info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth, vars, old = (active.loopdepth or 0) + 1, {}, {}
    for i = 1, n do
        local r = op.A + 2 + i; old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end
    local src
    local rs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A); local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, rs) then src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2)) end
    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do"); st.indent += 1
    for i = 1, n do local r = op.A + 2 + i; st.alias[r] = vars[i]; st.declared[vars[i]] = st.indent end
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then"); st.indent += 1
    local old = active.join; active.join = info.join
    self:_region(st, info.a, info.b, active); active.join = old
    st:trim(st.indent); st.indent -= 1
    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then self:_emitif(st, sub, active, "elseif"); return end
        st:out("else"); st.indent += 1; old = active.join; active.join = info.join
        self:_region(st, info.c, info.d, active); active.join = old
        st:trim(st.indent); st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start; active = active or {}
    local budgettick = 0
    while pc < stop and pc <= #st.proto.Instructions do
        budgettick += 1
        if budgettick >= 64 then budgettick = 0; self:_check() end
        if st.cfg.aux[pc] then pc += 1
        elseif st.consumed[pc] then st.v4.visited[pc] = true; pc += 1
        else
            st.v4.visited[pc] = true
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then


                st:hoist(pc)
                active["repeat:" .. tostring(pc)] = true; st:out("repeat"); st.indent += 1
                local prev = active.loop; active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active); active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch]); st.v4.visited[rep.latch] = true
                st:trim(st.indent); st.indent -= 1; st:out("until " .. ex.str(x)); active["repeat:" .. tostring(pc)] = nil; pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then

                    st:hoist(pc)
                    st:out("while true do"); st.indent += 1; local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active); active.loop = prev; st.v4.visited[forever.latch] = true
                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]; local name = ins.name(op)
                    if name == "FORNPREP" then pc = self:_numfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then pc = self:_genfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "CMPPROTO" then
                        local target, join = ins.jumpTarget(pc, op), st:join(pc)
                        if join and target > pc and target < join and join <= stop then self:_region(st, target, join, active); pc = join
                        else st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target)); pc = st:next(pc) end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop, target = active.loop, ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end"); pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc); st:out("while " .. ex.str(wh.cond) .. " do"); st.indent += 1
                                    local prev = active.loop; active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active); active.loop = prev
                                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then st:hoist(info.join); self:_emitif(st, info, active); pc = info.join
                                    else st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target)); pc = st:next(pc) end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target, loop = ins.jumpTarget(pc, op), active.loop
                        if loop and target == loop.breakpc then st:out("break"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("continue"); pc = st:next(pc)
                        elseif target == stop or target == active.join then pc = stop
                        else st:badpc(pc, "unstructured jump -> " .. tostring(target)); pc = st:next(pc) end
                    else pc = self:_op(st, pc) end
                end
            end
        end
    end
    return pc
end

local function dispatcherunsupported(st)
    for _, n in ipairs(st.ir.ops) do
        local name = n.name
        if name == "FORNPREP" or name == "FORNLOOP" or name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" or name == "FORGLOOP" then
            return "dispatcher requires VM loop-state emulation for " .. name .. " at pc " .. tostring(n.pc)
        end
        if name == "CMPPROTO" then return "CMPPROTO cannot be represented losslessly in source fallback at pc " .. tostring(n.pc) end
        if name == "CLOSEUPVALS" then return "dispatcher would change upvalue close/cell lifetime at pc " .. tostring(n.pc) end
        if name == "CAPTURE" and n.op.A == 1 then return "dispatcher would hoist a by-reference captured local cell at pc " .. tostring(n.pc) end
    end
end

function decomp:_dispatcher(st)
    local why = dispatcherunsupported(st)
    if why then error("LumenV4: UNSUPPORTED lossless fallback: " .. why, 2) end


    local nameset, ordered = {}, {}
    for id, v in ipairs(st.ir.vals) do
        if v and not st.ir.dead[id] and v.kind ~= "param" and v.kind ~= "undef" then
            local name = st:vname(id, v.reg, nil, v.pc or 1)
            if name and not nameset[name] and st.declared[name] == nil then nameset[name] = true; ordered[#ordered + 1] = name end
        end
    end
    table.sort(ordered)
    for i = 1, #ordered, 12 do
        local chunk = {}; for j = i, math.min(i + 11, #ordered) do chunk[#chunk + 1] = ordered[j]; st.declared[ordered[j]] = 0 end
        st:out("local " .. table.concat(chunk, ", "))
    end

    local state = st.naming:unique("__lumenstate")
    st.declared[state] = 0
    st:out("local " .. state .. " = 1")
    st:out("while true do"); st.indent += 1

    for bi, b in ipairs(st.cfg.blocks) do
        st:out((bi == 1 and "if " or "elseif ") .. state .. " == " .. tostring(b.id) .. " then")
        st.indent += 1
        st.top = nil
        for pi, pc in ipairs(b.pcs) do
            st.v4.visited[pc] = true
            if not st.consumed[pc] then
                local op, name = st.proto.Instructions[pc], ins.name(st.proto.Instructions[pc])
                local last = pi == #b.pcs
                if last and ins.isConditional(op) then
                    local target, fall = st.cfg.blockmap[ins.jumpTarget(pc, op)], st.cfg.blockmap[st:next(pc)]
                    if not target or not fall then error("LumenV4: invalid dispatcher conditional edge at pc " .. tostring(pc), 2) end
                    st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then")
                    st.indent += 1; st:out(state .. " = " .. tostring(target)); st.indent -= 1
                    st:out("else"); st.indent += 1; st:out(state .. " = " .. tostring(fall)); st.indent -= 1; st:out("end")
                elseif last and (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") then
                    local target = st.cfg.blockmap[ins.jumpTarget(pc, op)]
                    if not target then error("LumenV4: invalid dispatcher jump edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                elseif last and name == "LOADB" and (op.C or 0) ~= 0 then
                    self:_op(st, pc)
                    local target = st.cfg.blockmap[pc + op.C + 1]
                    if not target then error("LumenV4: invalid LOADB edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                else
                    self:_op(st, pc)
                    if last and name ~= "RETURN" then
                        if #b.successors == 1 then st:out(state .. " = " .. tostring(b.successors[1]))
                        elseif #b.successors == 0 then st:out("break")
                        elseif #b.successors > 1 then error("LumenV4: unhandled multi-successor block at pc " .. tostring(pc), 2) end
                    end
                end
            end
        end
        st.indent -= 1
    end
    st:out("else"); st.indent += 1; st:out("error(\"LumenV4: invalid dispatcher state \" .. tostring(" .. state .. "))"); st.indent -= 1
    st:out("end")
    st.indent -= 1; st:out("end")
end

local function metrics(st)
    local reachable, covered = 0, 0
    for pc = 1, #st.proto.Instructions do
        if not st.cfg.aux[pc] and st.cfg.blockmap[pc] then
            reachable += 1
            if st.v4.visited[pc] or st.consumed[pc] then covered += 1 end
        end
    end
    return reachable, covered, reachable == 0 and 1 or covered / reachable
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    local src = printer.run(root, self.opt)
    local reachable, covered, coverage = metrics(st)
    if covered ~= reachable then
        error(("LumenV4: PARTIAL origin coverage %d/%d (%.2f%%)"):format(covered, reachable, coverage * 100), 2)
    end
    local ss = st.ssa:summary()
    local structuredblocks = st.v4.fallback and 0 or #st.cfg.blocks
    local fallbackblocks = st.v4.fallback and #st.cfg.blocks or 0
    local objectcount, escapedobjects = 0, 0
    for _, obj in pairs(st.ir.objects or {}) do
        objectcount += 1
        if obj.escaped then escapedobjects += 1 end
    end
    local cellcount = 0
    for _ in pairs(st.ir.cells or {}) do cellcount += 1 end
    local packcount = 0
    for _, pack in pairs(st.ssa.packsByPC or {}) do if pack and pack.producesTop then packcount += 1 end end
    local irreducible = st.cfg.irreducible and 1 or 0
    local bytecodeversion = self.parsed and self.parsed.BytecodeVersion or 0

    if type(loadstring) ~= "function" then
        error("LumenV4: UNSUPPORTED syntax verification requires loadstring()", 2)
    end

    local header = ("-- LumenV4 status=%s coverage=%.2f reachable=%d covered=%d blocks=%d structuredBlocks=%d fallbackBlocks=%d phis=%d undefs=%d packs=%d cells=%d objects=%d escapedObjects=%d irreducible=%d bytecodeVersion=%d ssa=true parser=true diagnostics=%d\n")
        :format(st.v4.status, coverage * 100, reachable, covered, #st.cfg.blocks, structuredblocks, fallbackblocks,
            ss.phis or 0, ss.undefs or 0, packcount, cellcount, objectcount, escapedobjects, irreducible, bytecodeversion, #st.bad)
    src = header .. src
    local check, err = loadstring(src, "@LumenV4/verify")
    if not check then error("LumenV4: INVALID emitted Luau: " .. tostring(err), 2) end

    return src, {
        status = st.v4.status, cfg = st.cfg, ir = st.ir, ssa = st.ssa, ssaSummary = ss, issues = st.bad,
        coverage = coverage, coveredInstructions = covered, reachableInstructions = reachable, fallback = st.v4.fallback,
        syntaxValid = true, originCoverageValid = true, verification = "syntax+CFG-origin-invariants",
        objectCount = objectcount, escapedObjects = escapedobjects, cellCount = cellcount, valuePackCount = packcount,
        irreducible = st.cfg.irreducible == true, bytecodeVersion = bytecodeversion,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenV4: parsed bytecode has no entry proto")
    self.parsed = parsed

    local totalinstructions = 0
    local maxprotoinstructions = 0
    for _, p in ipairs(parsed.Protos or {}) do
        local n = #(p.Instructions or {})
        totalinstructions += n
        if n > maxprotoinstructions then maxprotoinstructions = n end
    end
    local maxtotal = tonumber(self.opt.structuredmaxinstructions) or 8000
    local maxproto = tonumber(self.opt.structuredmaxprotoinstructions) or 4000
    local structurederror
    if (maxtotal > 0 and totalinstructions > maxtotal) or (maxproto > 0 and maxprotoinstructions > maxproto) then
        structurederror = "LumenV4: STRUCTURED_COMPLEXITY total=" .. tostring(totalinstructions) .. " maxproto=" .. tostring(maxprotoinstructions)
    else
        local budget = tonumber(self.opt.structuredbudget) or 1.25
        self.slice = os.clock()
        self.deadline = budget > 0 and (self.slice + budget) or nil
        local ok, src, info = pcall(function() return self:decompileProto(proto, {}) end)
        self.deadline = nil
        if ok then
            self.parsed = nil
            return src, info
        end
        structurederror = tostring(src)
    end

    self.deadline = nil
    self.slice = os.clock()
    local fok, fsrc, finfo = pcall(function()
        return vmfallback.run(parsed, structurederror)
    end)
    self.parsed = nil

    if not fok then
        error("LumenV4: VM fallback generator failure after structured failure: " .. tostring(fsrc)
            .. " | structured: " .. structurederror, 2)
    end
    return fsrc, finfo
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
local bc = require("main.runtime.bytecode")
local tree = require("main.tree")
local config = require("main.config")

local dump = {}

local function accept(stat, source)
    stat.good += 1
    local status = source:match('^local __lumenmeta = "LumenV4 status=([A-Z_]+)')
    if status == "LOSSLESS_FALLBACK" or status == "VM_FALLBACK" then
        stat.fallback += 1
    elseif status == "STRUCTURED" then
        stat.structured += 1
    else
        stat.unknown += 1
    end
    local reachable, covered = source:match("reachable=(%d+) covered=(%d+)")
    stat.reachable += tonumber(reachable) or 0
    stat.covered += tonumber(covered) or 0
    local sb, fb = source:match("structuredBlocks=(%d+) fallbackBlocks=(%d+)")
    stat.sblocks += tonumber(sb) or 0
    stat.fblocks += tonumber(fb) or 0
    stat.phis += tonumber(source:match("phis=(%d+)")) or 0
    stat.packs += tonumber(source:match("packs=(%d+)")) or 0
    stat.cells += tonumber(source:match("cells=(%d+)")) or 0
    stat.objects += tonumber(source:match("objects=(%d+)")) or 0
    stat.escaped += tonumber(source:match("escapedObjects=(%d+)")) or 0
    stat.irreducible += tonumber(source:match("irreducible=(%d+)")) or 0
    local bv = tonumber(source:match("bytecodeVersion=(%d+)"))
    if bv then stat.versions[bv] = (stat.versions[bv] or 0) + 1 end
    if source:find("parser=true", 1, true) then stat.syntax += 1 end
end

local function rootdir()
    return "LumenDecomp/" .. tostring(game.PlaceId or 0) .. "/dump_" .. tostring(os.time())
end

local function write(path, data)
    if type(writefile) ~= "function" then return false, "executor does not expose writefile()" end
    local ok, err = pcall(writefile, path, data)
    return ok, err
end

local function decompfail(stat, cache, obj, err)
    err = tostring(err)
    stat.failed += 1
    if err:find("LumenV4: PARTIAL", 1, true) then stat.partial += 1
    elseif err:find("LumenV4: INVALID", 1, true) then stat.invalid += 1
    elseif err:find("LumenV4: UNSUPPORTED", 1, true) then stat.unsupported += 1
    else stat.other += 1 end
    cache[obj] = { success = false, error = err }
    local line = st.path(obj) .. " :: " .. err
    stat.errors[#stat.errors + 1] = line
    if stat.failed <= 5 then
        if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] FAIL " .. line .. "\n") end
        warn("[LumenDecomp] FAIL " .. line)
    end
end

local function unavailable(stat, cache, obj, err)
    err = tostring(err)
    stat.unavailable += 1
    if obj.ClassName == "Script" then stat.serverUnavailable += 1 end
    cache[obj] = { success = false, unavailable = true, error = err }
    local line = st.path(obj) .. " :: " .. err
    stat.unavailableErrors[#stat.unavailableErrors + 1] = line
end

local function acquire(list, stat, opt)
    local jobs = {}
    local cache = {}
    local started = os.clock()
    local slice = started
    local total = #list
    local batch = tonumber(opt.AcquireBatch)
    if not batch then
        if total >= 500 then batch = 3
        elseif total >= 200 then batch = 4
        elseif total >= 80 then batch = 6
        else batch = 12 end
    end
    batch = math.max(1, math.floor(batch))
    local budget = math.max(0.001, (tonumber(opt.AcquireBudgetMs) or 3) / 1000)
    stat.found = total
    stat.acquireBatch = batch
    stat.acquireBudgetMs = budget * 1000

    for i, obj in ipairs(list) do
        local ok, raw = bc.try(obj)
        if ok then
            if typeof(raw) == "buffer" then raw = buffer.tostring(raw) end
            jobs[#jobs + 1] = { obj = obj, raw = raw }
        else
            unavailable(stat, cache, obj, raw)
        end
        st.progress("Acquiring bytecode", obj, i, total)
        local now = os.clock()
        if i < total and (i % batch == 0 or now - slice >= budget) then
            stat.acquireYields += 1
            task.wait()
            slice = os.clock()
        end
    end

    stat.available = #jobs
    stat.acquireTime = os.clock() - started
    return jobs, cache
end

local function decopt(opt)
    local out = {}
    if type(opt.Options) == "table" then
        for k, v in pairs(opt.Options) do out[k] = v end
    end
    return out
end

local function warm(lumen, stat)
    local t = os.clock()
    local ok, err = pcall(function() return lumen:warm() end)
    stat.warmTime += os.clock() - t
    if not ok then return false, tostring(err) end
    return true
end

local function serial(lumen, jobs, opt, stat, cache, label)
    local ok, err = warm(lumen, stat)
    if not ok then
        for _, job in ipairs(jobs) do decompfail(stat, cache, job.obj, err) end
        stat.decompileTime = 0
        stat.rate = 0
        return cache
    end

    local started = os.clock()
    local cfg = decopt(opt)
    local total = #jobs
    local slice = os.clock()
    local budget = math.max(0.001, (tonumber(opt.DecompileBudgetMs) or 8) / 1000)
    for i, job in ipairs(jobs) do
        local res = lumen:tryDecompileBytecode(job.raw, cfg)
        if res.success and type(res.source) == "string" and res.source ~= "" then
            cache[job.obj] = res.source
            accept(stat, res.source)
        else
            decompfail(stat, cache, job.obj, res.error)
        end
        local elapsed = os.clock() - started
        st.progress(label or "Decompiling", job.obj, i, total, elapsed > 0 and i / elapsed or nil)
        if i < total and os.clock() - slice >= budget then
            task.wait()
            slice = os.clock()
        end
    end
    stat.decompileTime += os.clock() - started
    stat.rate = stat.decompileTime > 0 and stat.available / stat.decompileTime or 0
    return cache
end

local actorcode = [[
local id, src, vendor, smart, funcs, guards, fold, conds, blocks = ...
local ch = get_comm_channel(id)
local genv = type(getgenv) == "function" and getgenv() or _G
local okv, v = pcall(function()
    if type(vendor) ~= "string" or vendor == "" then return nil end
    local fn, err = loadstring(vendor, "@LumenIridiumVendor")
    assert(fn, err)
    return fn()
end)
if okv and type(v) == "table" then
    genv.__LUMEN_IRIDIUM_VENDOR = v
    _G.__LUMEN_IRIDIUM_VENDOR = v
end
local ok, api = pcall(function()
    local fn, err = loadstring(src, "@LumenWorker")
    assert(fn, err)
    return fn()
end)
if not ok then
    ch:Fire("boot", false, tostring(api))
    return
end
local wok, werr = pcall(function() return api:warm() end)
if not wok then
    ch:Fire("boot", false, tostring(werr))
    return
end
genv.__LUMEN_IRIDIUM_VENDOR = nil
_G.__LUMEN_IRIDIUM_VENDOR = nil
local dec = {
    smartnames = smart,
    functions = funcs,
    guards = guards,
    fold = fold,
    conditions = conds,
    doblocks = blocks,
}
local con
con = ch.Event:Connect(function(kind, jid, raw)
    if kind == "stop" then
        if con then con:Disconnect() end
        return
    end
    if kind ~= "job" then return end
    local good, out = pcall(function() return api:decompileBytecode(raw, dec) end)
    if good and type(out) == "string" and out ~= "" then
        ch:Fire("done", jid, true, out)
    else
        ch:Fire("done", jid, false, tostring(out))
    end
end)
ch:Fire("boot", true, "")
]]

local function getpool()
    local pool = {}
    if type(getactors) ~= "function" then return pool end
    local ok, list = pcall(getactors)
    if not ok or type(list) ~= "table" then return pool end
    for _, a in ipairs(list) do
        if typeof(a) == "Instance" and a:IsA("Actor") then pool[#pool + 1] = a end
    end
    return pool
end

local function actors(lumen, jobs, opt, stat, cache)
    if opt.Parallel == false then return nil, "disabled" end
    if #jobs < 12 then return nil, "small corpus fast path" end
    if type(run_on_actor) ~= "function" or type(create_comm_channel) ~= "function" or type(get_comm_channel) ~= "function" then
        return nil, "Potassium actor APIs unavailable"
    end
    if type(lumen._workerSource) ~= "function" or type(lumen._iridiumPack) ~= "function" then
        return nil, "worker source unavailable"
    end

    local max = tonumber(opt.MaxWorkers) or 4
    max = math.max(2, math.min(math.floor(max), 32))
    local useful = math.max(2, math.floor(#jobs / 4))
    local want = math.min(max, 16, useful)

    local bootstart = os.clock()
    local vendor, verr = lumen:_iridiumPack()
    if type(vendor) ~= "string" then return nil, "Iridium prefetch failed: " .. tostring(verr) end
    stat.warmTime += os.clock() - bootstart

    local pool = getpool()
    if #pool < 2 then return nil, "fewer than 2 executor-reported Actors" end

    local src = lumen:_workerSource()
    if type(src) ~= "string" or src == "" then return nil, "empty worker source" end

    local ws = {}
    local live = {}
    local dc = config(decopt(opt))
    local q = {}
    local qhead = 1
    local qtail = 0
    local why = {}

    for _, actor in ipairs(pool) do
        if #live >= want then break end
        local id, ch = create_comm_channel()
        local w = { id = id, ch = ch, actor = actor, ready = false, dead = false, busy = false, sent = 0 }
        w.con = ch.Event:Connect(function(kind, a, b, c)
            if kind == "boot" then
                if a then w.ready = true else w.dead = true; w.err = tostring(b) end
            elseif kind == "done" then
                qtail += 1
                q[qtail] = { w = w, jid = a, ok = b, out = c }
            end
        end)
        ws[#ws + 1] = w
        local rok, rerr = pcall(run_on_actor, actor, actorcode, id, src, vendor, dc.smartnames ~= false, dc.functions ~= false, dc.guards ~= false, dc.fold ~= false, dc.conditions ~= false, dc.doblocks or 0)
        if not rok then
            w.dead = true
            w.err = tostring(rerr)
        else
            local bt = os.clock()
            while not w.ready and not w.dead and os.clock() - bt < 3 do task.wait(0.01) end
            if not w.ready then
                w.dead = true
                w.err = w.err or "worker boot timeout"
            end
        end
        if w.ready and not w.dead then
            live[#live + 1] = w
            task.wait()
        else
            why[#why + 1] = w.err or "unusable Actor"
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
    end

    stat.parallelBootTime = os.clock() - bootstart
    if #live < 2 then
        for _, w in ipairs(ws) do
            if w.ready then pcall(function() w.ch:Fire("stop") end) end
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
        return nil, "worker boot failed" .. (#why > 0 and (": " .. table.concat(why, " | ")) or "")
    end

    stat.parallel = #live
    local nextjob = 1
    local done = 0
    local active = {}
    local retry = {}
    local started = os.clock()

    local function send(w)
        if w.dead or nextjob > #jobs then return end
        local jid = nextjob
        nextjob += 1
        w.busy = true
        w.sent = os.clock()
        w.jid = jid
        active[jid] = true
        w.ch:Fire("job", jid, jobs[jid].raw)
    end

    for _, w in ipairs(live) do send(w) end

    while done < #jobs do
        while qhead <= qtail do
            local r = q[qhead]
            q[qhead] = nil
            qhead += 1
            local w = r.w
            local jid = r.jid
            if active[jid] then
                active[jid] = nil
                done += 1
                w.busy = false
                local job = jobs[jid]
                if r.ok and type(r.out) == "string" and r.out ~= "" then
                    cache[job.obj] = r.out
                    accept(stat, r.out)
                else
                    retry[#retry + 1] = job
                end
                local elapsed = os.clock() - started
                st.progress("Parallel decompile x" .. tostring(#live), job.obj, done, #jobs, elapsed > 0 and done / elapsed or nil)
                send(w)
            end
        end

        local now = os.clock()
        for _, w in ipairs(live) do
            if w.busy and now - w.sent > 45 then
                local jid = w.jid
                if active[jid] then
                    active[jid] = nil
                    w.dead = true
                    w.busy = false
                    done += 1
                    retry[#retry + 1] = jobs[jid]
                end
            end
        end

        local alive = 0
        for _, w in ipairs(live) do if not w.dead then alive += 1 end end
        if alive == 0 then
            for jid = nextjob, #jobs do retry[#retry + 1] = jobs[jid] end
            done = #jobs
            break
        end
        task.wait(0.002)
    end

    for _, w in ipairs(ws) do
        pcall(function() w.ch:Fire("stop") end)
        if w.con then pcall(function() w.con:Disconnect() end) end
    end
    task.wait()

    stat.decompileTime += os.clock() - started

    if #retry > 0 then
        local wok, werr = warm(lumen, stat)
        if not wok then
            for _, job in ipairs(retry) do decompfail(stat, cache, job.obj, werr) end
        else
            local cfg = decopt(opt)
            local rs = os.clock()
            for i, job in ipairs(retry) do
                local res = lumen:tryDecompileBytecode(job.raw, cfg)
                if res.success and type(res.source) == "string" and res.source ~= "" then
                    cache[job.obj] = res.source
                    accept(stat, res.source)
                else
                    decompfail(stat, cache, job.obj, res.error)
                end
                st.progress("Retrying locally", job.obj, i, #retry)
            end
            stat.decompileTime += os.clock() - rs
        end
    end

    stat.rate = stat.decompileTime > 0 and stat.available / stat.decompileTime or 0
    return cache
end

local function writetree(root, list, cache, treeon, stat, made, opt)
    local ctx = tree.new(root, made, opt.MaxPathLength or 240, list)
    local started = os.clock()
    local written = 0
    local source = 0
    local placeholders = 0
    local slice = os.clock()
    local budget = math.max(0.001, (tonumber(opt.WriteBudgetMs) or 8) / 1000)

    for i, obj in ipairs(list) do
        local v = cache[obj]
        local body
        local state
        if type(v) == "string" then
            body = v
            state = "decompiled"
            source += 1
        elseif type(v) == "table" then
            body = tree.placeholder(obj, v)
            state = v.unavailable and "unavailable" or "failed"
            placeholders += 1
        else
            body = tree.placeholder(obj, { error = "no decompile result" })
            state = "missing"
            placeholders += 1
        end

        local path = tree.path(ctx, obj, treeon)
        local ok, err = write(path, body)
        if ok then
            written += 1
        else
            stat.writeFailed += 1
            stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. tostring(err)
            state = "write-failed"
        end
        tree.record(ctx, obj, path, state)
        st.progress("Writing source tree", obj, i, #list)
        if i < #list and os.clock() - slice >= budget then
            task.wait()
            slice = os.clock()
        end
    end

    local mok, merr = write(root .. "/tree-map.tsv", tree.map(ctx))
    if not mok then
        stat.writeFailed += 1
        stat.errors[#stat.errors + 1] = "tree-map.tsv :: " .. tostring(merr)
    end

    stat.written = written
    stat.sourceWritten = source
    stat.placeholderWritten = placeholders
    stat.writeTime = os.clock() - started
end

local function summary(root, stat)
    local lines = {
        "LumenDecomp dump",
        "PlaceId: " .. tostring(game.PlaceId),
        "Script instances found: " .. tostring(stat.found),
        "Bytecode available: " .. tostring(stat.available),
        "Accepted source (syntax + origin coverage): " .. tostring(stat.good),
        "Structured accepted: " .. tostring(stat.structured),
        "Lossless/VM fallback accepted: " .. tostring(stat.fallback),
        "Partial: " .. tostring(stat.partial),
        "Invalid output: " .. tostring(stat.invalid),
        "Unsupported: " .. tostring(stat.unsupported),
        "Other failures: " .. tostring(stat.other),
        "Syntax-valid source: " .. tostring(stat.syntax) .. "/" .. tostring(stat.good),
        "Reachable instruction coverage: " .. (stat.reachable > 0 and string.format("%.2f%%", stat.covered * 100 / stat.reachable) or "100.00%"),
        "Structured blocks: " .. tostring(stat.sblocks),
        "Fallback blocks: " .. tostring(stat.fblocks),
        "Phi nodes: " .. tostring(stat.phis),
        "ValuePack producers: " .. tostring(stat.packs),
        "Captured cells: " .. tostring(stat.cells),
        "Tracked heap objects: " .. tostring(stat.objects),
        "Escaped heap objects: " .. tostring(stat.escaped),
        "Irreducible accepted functions: " .. tostring(stat.irreducible),
        "Decompile failures: " .. tostring(stat.failed),
        "Bytecode unavailable: " .. tostring(stat.unavailable),
        "Server Script unavailable: " .. tostring(stat.serverUnavailable),
        "Tree files written: " .. tostring(stat.written or 0),
        "Decompiled source files: " .. tostring(stat.sourceWritten or 0),
        "Placeholder files: " .. tostring(stat.placeholderWritten or 0),
        "Tree scan failures: " .. tostring(stat.scanFailed or 0),
        "Write failures: " .. tostring(stat.writeFailed),
        "Binary: " .. tostring(stat.binary),
        "Workers: " .. tostring(stat.parallel or 1),
        "SmartVariableRenamer: " .. tostring(stat.decompiler and stat.decompiler.smartnames ~= false),
        "FunctionDeclarations: " .. tostring(stat.decompiler and stat.decompiler.functions ~= false),
        "GuardClauses: " .. tostring(stat.decompiler and stat.decompiler.guards ~= false),
        "ConstantFolding: " .. tostring(stat.decompiler and stat.decompiler.fold ~= false),
        "ConditionalStructurer: " .. tostring(stat.decompiler and stat.decompiler.conditions ~= false),
        "DoBlockInsertionThreshold: " .. tostring(stat.decompiler and stat.decompiler.doblocks or 0),
        "Acquire seconds: " .. string.format("%.3f", stat.acquireTime or 0),
        "Acquire batch: " .. tostring(stat.acquireBatch or 0),
        "Acquire budget ms: " .. string.format("%.2f", stat.acquireBudgetMs or 0),
        "Acquire yields: " .. tostring(stat.acquireYields or 0),
        "Warmup seconds: " .. string.format("%.3f", stat.warmTime or 0),
        "Worker boot seconds: " .. string.format("%.3f", stat.parallelBootTime or 0),
        "Reconstruct seconds: " .. string.format("%.3f", stat.decompileTime or 0),
        "Reconstruct rate: " .. string.format("%.2f scripts/s", stat.rate or 0),
        "Write seconds: " .. string.format("%.3f", stat.writeTime or 0),
        "Total seconds: " .. string.format("%.3f", stat.totalTime or 0),
        "",
    }
    if #stat.errors > 0 then
        lines[#lines + 1] = "Decompile/write errors:"
        for _, e in ipairs(stat.errors) do lines[#lines + 1] = e end
        lines[#lines + 1] = ""
    end
    if #stat.unavailableErrors > 0 then
        lines[#lines + 1] = "Unavailable bytecode:"
        for _, e in ipairs(stat.unavailableErrors) do lines[#lines + 1] = e end
    end
    write(root .. "/summary.txt", table.concat(lines, "\n"))
end

function dump.run(lumen, opt)
    opt = opt or {}
    local totalstart = os.clock()
    local root = opt.Root or rootdir()
    local stat = {
        found = 0,
        available = 0,
        good = 0,
        structured = 0,
        fallback = 0,
        unknown = 0,
        partial = 0,
        invalid = 0,
        unsupported = 0,
        other = 0,
        syntax = 0,
        reachable = 0,
        covered = 0,
        sblocks = 0,
        fblocks = 0,
        phis = 0,
        packs = 0,
        cells = 0,
        objects = 0,
        escaped = 0,
        irreducible = 0,
        versions = {},
        failed = 0,
        unavailable = 0,
        serverUnavailable = 0,
        written = 0,
        sourceWritten = 0,
        placeholderWritten = 0,
        scanFailed = 0,
        writeFailed = 0,
        binary = false,
        errors = {},
        unavailableErrors = {},
        acquireTime = 0,
        acquireBatch = 0,
        acquireBudgetMs = 0,
        acquireYields = 0,
        warmTime = 0,
        parallelBootTime = 0,
        decompileTime = 0,
        writeTime = 0,
        totalTime = 0,
        rate = 0,
        parallel = 1,
        decompiler = config(decopt(opt)),
    }
    local made = {}
    tree.mkall(root, made)
    st.set("Starting", tostring(game.Name) .. " | " .. root)

    local list
    local cache
    if opt.Decompile and (opt.Tree or not opt.Binary) then
        local scanerr
        list, scanerr = tree.scan(opt.IgnoreCoreScripts == true, coref)
        stat.scanFailed = #scanerr
        for _, e in ipairs(scanerr) do stat.errors[#stat.errors + 1] = "scan :: " .. tostring(e) end
        local jobs
        jobs, cache = acquire(list, stat, opt)

        if #jobs > 0 then
            local pok, pout, preason = pcall(actors, lumen, jobs, opt, stat, cache)
            if pok then
                if pout then
                    cache = pout
                elseif preason and opt.Parallel ~= false then
                    if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel: " .. tostring(preason) .. "\n") end
                end
            else
                if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel fallback: " .. tostring(pout) .. "\n") end
                warn("[LumenDecomp] parallel fallback: " .. tostring(pout))
            end
            if stat.good + stat.failed < #jobs then
                local pending = {}
                for _, job in ipairs(jobs) do
                    if cache[job.obj] == nil then pending[#pending + 1] = job end
                end
                serial(lumen, pending, opt, stat, cache, "Decompiling")
            end
        end

        writetree(root, list, cache, opt.Tree, stat, made, opt)
    end

    if opt.Binary then
        st.set("Saving binary", cache and "reusing source/availability cache" or tostring(game.Name))
        task.wait()
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
                MaxThreads = opt.MaxThreads or 3,
                DecompileIgnore = opt.IgnoreCoreScripts and { "Chat", "CoreGui", "CorePackages", "RobloxReplicatedStorage", "CoreScriptSyncService" } or opt.DecompileIgnore,
                ShowStatus = false,
            })
        end)
        stat.binary = ok
        if not ok then stat.errors[#stat.errors + 1] = "binary :: " .. tostring(err) end
    end

    stat.totalTime = os.clock() - totalstart
    summary(root, stat)
    local mode = stat.parallel and stat.parallel > 1 and (" x" .. tostring(stat.parallel)) or ""
    if stat.failed > 0 then
        st.done("Done - " .. tostring(stat.good) .. " decompiled, " .. tostring(stat.failed) .. " failed, " .. tostring(stat.unavailable) .. " unavailable | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
    else
        st.done("Done - " .. tostring(stat.good) .. " decompiled, 0 failed, " .. tostring(stat.unavailable) .. " unavailable | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
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
    local maxthreads = tonumber(val("MaxThreads")) or 3
    maxthreads = math.max(1, math.min(math.floor(maxthreads), 8))
    local maxpath = tonumber(val("MaxPathLength")) or 240
    local acquirebatch = tonumber(val("AcquireBatch"))
    local acquirebudget = tonumber(val("AcquireBudgetMs")) or 3
    local decompilebudget = tonumber(val("DecompileBudgetMs")) or 8
    local writebudget = tonumber(val("WriteBudgetMs")) or 8
    local dopt = val("DecompilerOptions")
    if type(dopt) ~= "table" then dopt = {} end
    local names = { "SmartVariableRenamer", "FunctionDeclarations", "GuardClauses", "ConstantFolding", "ConditionalStructurer", "DoBlockInsertionThreshold" }
    for _, name in ipairs(names) do
        local v = val(name)
        if v ~= nil then dopt[name] = v end
    end
    local flags = "Binary=" .. tostring(binary) .. " | Decompile=" .. tostring(decomp) .. " | Tree=" .. tostring(treeon) .. " | IgnoreCoreScripts=" .. tostring(ignorecore) .. " | Parallel=" .. tostring(parallel) .. " | MaxWorkers=" .. tostring(maxworkers) .. " | MaxThreads=" .. tostring(maxthreads)

    st.set("Loaded", "v" .. tostring(lumen.Version) .. " | " .. flags)
    print("[LumenDecomp] " .. flags)
    local dc = config(dopt)
    print("[LumenDecomp] SmartVariableRenamer=" .. tostring(dc.smartnames ~= false) .. " | FunctionDeclarations=" .. tostring(dc.functions ~= false) .. " | GuardClauses=" .. tostring(dc.guards ~= false) .. " | ConstantFolding=" .. tostring(dc.fold ~= false) .. " | ConditionalStructurer=" .. tostring(dc.conditions ~= false) .. " | DoBlockInsertionThreshold=" .. tostring(dc.doblocks or 0))
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
            dump.run(lumen, { Binary = binary, Decompile = decomp, Tree = treeon, IgnoreCoreScripts = ignorecore, Parallel = parallel, MaxWorkers = maxworkers, MaxThreads = maxthreads, MaxPathLength = maxpath, AcquireBatch = acquirebatch, AcquireBudgetMs = acquirebudget, DecompileBudgetMs = decompilebudget, WriteBudgetMs = writebudget, Options = dopt })
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
    ["main.ir.build"] = [===[local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local regs = require("main.analysis.registers")
local ins = require("main.bytecode.instructions")
local fx = require("main.ir.effects")
local fn = require("main.ir.function")
local val = require("main.ir.value")
local block = require("main.ir.block")

local build = {}

local function copyset(src)
    local out = {}; if src then for k in pairs(src) do out[k] = true end end; return out
end
local function unionset(dst, src)
    local changed = false
    if src then for k in pairs(src) do if not dst[k] then dst[k] = true; changed = true end end end
    return changed
end
local function seteq(a, b)
    a, b = a or {}, b or {}
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end


local function copystate(src)
    local out = {}
    for r, set in pairs(src or {}) do out[r] = copyset(set) end
    return out
end

local function stateeq(a, b)
    a, b = a or {}, b or {}
    for r, set in pairs(a) do if not seteq(set, b[r]) then return false end end
    for r, set in pairs(b) do if not seteq(set, a[r]) then return false end end
    return true
end


local function analyzecells(out, check)
    local capturecell, capturereg, nextcell = {}, {}, 1
    for _, n in ipairs(out.ops) do
        if n.name == "CAPTURE" and n.op.A == 1 then
            capturecell[n.pc] = nextcell
            capturereg[nextcell] = n.op.B
            nextcell += 1
        end
    end

    if nextcell == 1 then
        out.cells, out.cellOfValue, out.captureCell = {}, {}, capturecell
        return out
    end

    local instate, outstate = {}, {}
    local function merged(block)
        if block.id == 1 then return {} end
        local result = {}
        for _, pred in ipairs(block.predecessors) do
            for r, set in pairs(outstate[pred] or {}) do
                local dst = result[r]
                if not dst then dst = {}; result[r] = dst end
                unionset(dst, set)
            end
        end
        return result
    end

    local function transfer(block, incoming)
        local state = copystate(incoming)
        for _, pc in ipairs(block.pcs) do
            local op = out.proto.Instructions[pc]
            local name = ins.name(op)
            if name == "CAPTURE" and op.A == 1 then
                local set = state[op.B]
                if not set then set = {}; state[op.B] = set end
                set[capturecell[pc]] = true
            elseif name == "CLOSEUPVALS" then
                for r in pairs(state) do if r >= (op.A or 0) then state[r] = nil end end
            end
        end
        return state
    end

    local changed, iterations = true, 0
    local limit = math.max(32, #out.cfg.blocks * (nextcell + 8) * 4)
    while changed do
        if check then check() end
        iterations += 1
        if iterations > limit then error("LumenV4: CellId dataflow failed to converge", 2) end
        changed = false
        for _, b in ipairs(out.cfg.blocks) do
            local incoming = merged(b)
            if not stateeq(instate[b.id], incoming) then instate[b.id] = incoming; changed = true end
            local outgoing = transfer(b, incoming)
            if not stateeq(outstate[b.id], outgoing) then outstate[b.id] = outgoing; changed = true end
        end
    end

    local valuecells, closesites = {}, {}
    local function markvalue(version, set)
        if not version or not set or not next(set) then return end
        local dst = valuecells[version]
        if not dst then dst = {}; valuecells[version] = dst end
        unionset(dst, set)
    end

    for _, b in ipairs(out.cfg.blocks) do
        local state = copystate(instate[b.id])
        for _, pc in ipairs(b.pcs) do
            local op = out.proto.Instructions[pc]
            local name = ins.name(op)
            local uses = out.ssa.usesByPC[pc] or {}
            local defs = out.ssa.defsByPC[pc] or {}

            if name == "CAPTURE" and op.A == 1 then
                local set = state[op.B]
                if not set then set = {}; state[op.B] = set end
                set[capturecell[pc]] = true
            end

            for r, version in pairs(uses) do markvalue(version, state[r]) end
            for r, version in pairs(defs) do markvalue(version, state[r]) end

            if name == "CLOSEUPVALS" then
                for r, set in pairs(state) do
                    if r >= (op.A or 0) then
                        for cid in pairs(set) do
                            local list = closesites[cid]
                            if not list then list = {}; closesites[cid] = list end
                            list[pc] = true
                        end
                        state[r] = nil
                    end
                end
            end
        end
    end

    local parent = {}
    for cid = 1, nextcell - 1 do parent[cid] = cid end
    local function root(x)
        local p = parent[x]
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end
    local function join(a, b)
        a, b = root(a), root(b)
        if a ~= b then if a < b then parent[b] = a else parent[a] = b end end
    end
    local function joinset(set)
        local first
        for cid in pairs(set or {}) do if first then join(first, cid) else first = cid end end
    end
    for _, set in pairs(valuecells) do joinset(set) end
    for _, state in pairs(instate) do for _, set in pairs(state) do joinset(set) end end
    for _, state in pairs(outstate) do for _, set in pairs(state) do joinset(set) end end

    local cells, cellofvalue = {}, {}
    for pc, cid in pairs(capturecell) do
        local rid = root(cid)
        capturecell[pc] = rid
        local c = cells[rid]
        if not c then c = { id = rid, reg = capturereg[cid], captures = {}, closes = {}, values = {} }; cells[rid] = c end
        c.captures[#c.captures + 1] = pc
    end
    for version, set in pairs(valuecells) do
        local rid
        for cid in pairs(set) do rid = root(cid); break end
        if rid then
            cellofvalue[version] = rid
            local c = cells[rid]
            if not c then c = { id = rid, reg = capturereg[rid], captures = {}, closes = {}, values = {} }; cells[rid] = c end
            c.values[version] = true
        end
    end
    for cid, sites in pairs(closesites) do
        local rid = root(cid)
        local c = cells[rid]
        if c then for pc in pairs(sites) do c.closes[pc] = true end end
    end
    for _, c in pairs(cells) do table.sort(c.captures) end

    out.cells = cells
    out.cellOfValue = cellofvalue
    out.captureCell = capturecell
    out.cellInState = instate
    out.cellOutState = outstate
    out.cellIterations = iterations
    function out:cellId(valueid) return self.cellOfValue[valueid] or self.cellOfValue[self:resolve(valueid)] end
    return out
end

local function analyzeobjects(out, check)
    local sets, objects, nextobject = {}, {}, 1
    local function def(pc, reg)
        local d = out.ssa.defsByPC[pc]; return d and d[reg] or nil
    end
    local function use(pc, reg)
        local u = out.ssa.usesByPC[pc]; return u and u[reg] or nil
    end
    local function assign(id, nextset)
        if not id then return false end
        if not seteq(sets[id], nextset) then sets[id] = copyset(nextset); return true end
        return false
    end

    for _, n in ipairs(out.ops) do
        if n.name == "NEWTABLE" or n.name == "DUPTABLE" or n.name == "NEWCLASS" then
            local id = def(n.pc, n.op.A)
            if id then
                local oid = nextobject; nextobject += 1
                objects[oid] = { id = oid, allocPC = n.pc, kind = n.name, escaped = false, escapePCs = {}, aliases = {} }
                sets[id] = { [oid] = true }
            end
        end
    end

    local changed, iterations = true, 0
    local limit = math.max(32, #out.ops * 8 + 32)
    while changed do
        if check then check() end
        iterations += 1; if iterations > limit then error("LumenV4: ObjectId propagation failed to converge", 2) end
        changed = false
        for _, n in ipairs(out.ops) do
            if n.name == "MOVE" then
                changed = assign(def(n.pc, n.op.A), sets[use(n.pc, n.op.B)]) or changed
            elseif n.name == "NAMECALL" or n.name == "NAMECALLUDATA" then

                changed = assign(def(n.pc, n.op.A + 1), sets[use(n.pc, n.op.B)]) or changed
            end
        end
        for _, phis in pairs(out.phis) do
            for _, phi in pairs(phis) do
                local merged = {}
                for raw in pairs(phi.inputs or {}) do unionset(merged, sets[raw]) end
                changed = assign(phi.id, merged) or changed
            end
        end
    end

    local function mark(id, pc, reason)
        for oid in pairs(sets[id] or {}) do
            local obj = objects[oid]
            obj.escaped = true
            obj.escapePCs[pc] = reason or true
        end
    end


    for id, os in pairs(sets) do for oid in pairs(os) do objects[oid].aliases[id] = true end end
    for _, n in ipairs(out.ops) do
        local pc, op, name = n.pc, n.op, n.name
        local reads = out.ssa.usesByPC[pc] or {}
        local safebase = {}
        if name == "GETTABLE" or name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then safebase[op.B] = true
        elseif name == "SETTABLE" or name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then safebase[op.B] = true
        elseif name == "SETLIST" then safebase[op.A] = true
        elseif name == "NAMECALL" or name == "NAMECALLUDATA" then safebase[op.B] = true
        elseif name == "MOVE" then safebase[op.B] = true
        end

        for reg, id in pairs(reads) do
            if sets[id] and not safebase[reg] then
                local reason = name
                if name == "CALL" or name == "CALLFB" then reason = "CallUnknown"
                elseif name == "RETURN" then reason = "Return"
                elseif name == "CAPTURE" then reason = "Capture"
                elseif name == "SETGLOBAL" or name == "SETUPVAL" then reason = "StoreExternal"
                elseif name:match("^SETTABLE") or name == "SETUDATAKS" or name == "SETLIST" then reason = "StoreHeap" end
                mark(id, pc, reason)
            end
        end
    end

    out.objectSets = sets
    out.objects = objects
    out.objectIterations = iterations
    function out:objectIds(valueid) return self.objectSets[self:resolve(valueid)] or {} end
    function out:objectId(valueid)
        local one
        for oid in pairs(self:objectIds(valueid)) do if one then return nil end; one = oid end
        return one
    end
    return out
end

function build.run(proto, check, limits)
    local cfg = graph.build(proto, check, limits)
    local flow = ssa.build(proto, cfg, check, limits)
    assert(flow.converged, "LumenV4: refusing non-converged SSA")
    local out = fn.new(proto, cfg, flow)
    for id, src in ipairs(flow.versions) do
        out.vals[id] = val.new(id, src)
        if src.dead then out.dead[id] = true end
        if src.kind == "undef" then out.const[id] = "nil"; out.inline[id] = true end
    end
    for bid, phis in pairs(flow.phisByBlock) do
        local dst = {}; out.phis[bid] = dst
        for reg, p in pairs(phis) do
            dst[reg] = { id = p.id, reg = reg, inputs = p.inputs, incoming = p.incoming, missing = p.missing }
        end
    end
    for _, src in ipairs(cfg.blocks) do
        local b = block.new(src); out.blocks[b.id] = b
        for _, pc in ipairs(src.pcs) do
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local reads, writes, pack = regs.readWrite(op)
            local n = { pc = pc, op = op, name = name, block = b.id, reads = reads, writes = writes, pack = pack,
                pure = fx.pure(name), drop = fx.drop(name), quiet = fx.quiet(name), effect = fx.effect(name), term = fx.term(name) }
            out.ops[#out.ops + 1] = n; out.bypc[pc] = n; b.ops[#b.ops + 1] = n
        end
    end
    out:reindex()
    analyzecells(out, check)
    analyzeobjects(out, check)
    return out
end
return build
]===],
    ["main.ir.effects"] = [===[
local fx = {}

local relocatable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,

    MOVE = true,
}

local discardable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true, MOVE = true,
    NOT = true, AND = true, OR = true, ANDK = true, ORK = true,


}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, PREPVARARGS = true, COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

local effects = {
    GETGLOBAL = "ReadGlobal", SETGLOBAL = "WriteGlobal",
    GETUPVAL = "ReadCell", SETUPVAL = "WriteCell", CLOSEUPVALS = "CloseCells", CAPTURE = "CaptureCell",
    GETTABLE = "ReadTable", GETTABLEKS = "ReadTable", GETTABLEN = "ReadTable", GETUDATAKS = "ReadTable",
    SETTABLE = "WriteTable", SETTABLEKS = "WriteTable", SETTABLEN = "WriteTable", SETUDATAKS = "WriteTable",
    CALL = "CallUnknown", CALLFB = "CallUnknown", NAMECALL = "ReadTable", NAMECALLUDATA = "ReadTable",
    NEWCLOSURE = "AllocateClosure", DUPCLOSURE = "AllocateClosure",
    NEWTABLE = "AllocateObject", DUPTABLE = "AllocateObject", NEWCLASS = "AllocateObject", NEWCLASSMEMBER = "WriteTable",
    ADD = "MayMetamethod", SUB = "MayMetamethod", MUL = "MayMetamethod", DIV = "MayMetamethod", MOD = "MayMetamethod",
    POW = "MayMetamethod", IDIV = "MayMetamethod", ADDK = "MayMetamethod", SUBK = "MayMetamethod", MULK = "MayMetamethod",
    DIVK = "MayMetamethod", MODK = "MayMetamethod", POWK = "MayMetamethod", IDIVK = "MayMetamethod",
    SUBRK = "MayMetamethod", DIVRK = "MayMetamethod", CONCAT = "MayMetamethod", LENGTH = "MayMetamethod",
    GETIMPORT = "ReadImport", NATIVECALL = "CallUnknown",
}

function fx.pure(name) return relocatable[name] == true end
function fx.drop(name) return discardable[name] == true end
function fx.quiet(name) return quiet[name] == true end
function fx.term(name) return term[name] == true end
function fx.class(name)
    if term[name] then return "Control" end
    return effects[name] or (quiet[name] and "Pure" or "Unknown")
end
function fx.effect(name)
    local c = fx.class(name)
    return c ~= "Pure" and c ~= "Control"
end
function fx.canRelocate(name) return relocatable[name] == true end

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

    if self.opt.smartnames == false then
        if pc == 1 and reg < (self.proto.ParameterCount or 0) then return self:unique("arg" .. tostring(reg + 1)) end
        return self:name(reg, nil)
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
    if self.opt.smartnames ~= false and hint and self:stable(reg) then base = id.clean(hint) end
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
    ["main.options"] = [===[
local opt = {}

function opt.new()
    return {
        SmartVariableRenamer = true,
        FunctionDeclarations = true,
        GuardClauses = true,
        ConstantFolding = true,
        ConditionalStructurer = true,
        DoBlockInsertionThreshold = 0,
    }
end

return opt
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

function pass.run(ir, check)
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
        if check then check() end
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
    ["main.passes.inline"] = [===[local ins = require("main.bytecode.instructions")

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

local function mutablevalues(ir, check)
    local mutable = {}
    local changed = true


    for id, objectset in pairs(ir.objectSets or {}) do
        if next(objectset) then
            local resolved = ir:resolve(id)
            if resolved then mutable[resolved] = true end
        end
    end

    for _, n in ipairs(ir.ops) do
        if n.name == "NEWTABLE" or n.name == "DUPTABLE" or n.name == "NEWCLASS" then
            local defs = ir.ssa.defsByPC[n.pc] or {}
            local v = ir:resolve(defs[n.op.A])
            if v then mutable[v] = true end
        end
    end

    while changed do
        if check then check() end
        changed = false
        for _, n in ipairs(ir.ops) do
            if n.name == "MOVE" then
                local uses = ir.ssa.usesByPC[n.pc] or {}
                local defs = ir.ssa.defsByPC[n.pc] or {}
                local src = ir:resolve(uses[n.op.B])
                local dst = ir:resolve(defs[n.op.A])
                if src and dst and mutable[src] and not mutable[dst] then mutable[dst] = true; changed = true end
            end
        end
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                local pid = ir:resolve(p.id)
                if pid and not mutable[pid] then
                    for raw in pairs(p.inputs or {}) do
                        local src = ir:resolve(raw)
                        if src and mutable[src] then mutable[pid] = true; changed = true break end
                    end
                end
            end
        end
    end
    return mutable
end

function pass.run(ir, check)
    local mutable = mutablevalues(ir, check)
    ir.mutableObjects = mutable

    for id, v in pairs(ir.vals) do
        if check then check() end
        id = ir:resolve(id)
        if id and not ir.dead[id] and v.kind == "def" and not mutable[id] then
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
        id = ir:resolve(id)
        if id and not mutable[id] then
            local ok = ir:count(id) > 0
            for _, u in ipairs(ir:uses(id) or {}) do
                local useop = u.pc and ir.bypc[u.pc] or nil
                if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
            end
            if ok then ir.inline[id] = true end
        end
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

local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt, check)
    opt = opt or {}


    if check then check() end
    if opt.dce ~= false then dead.run(ir, check) end
    if check then check() end


    names.run(ir)
    if check then check() end
    if opt.smartnames ~= false then
        prov.run(ir)
        if check then check() end
    else
        ir.bestname, ir.namescore, ir.hints, ir.origin = {}, {}, {}, {}
    end

    if opt.inline ~= false then inline.run(ir, check) end
    if check then check() end
    cond.run(ir)
    if check then check() end
    flow.run(ir)
    if check then check() end
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
    ["main.recover.branches"] = [===[local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end

    local join = st:join(pc)

    if not join or join <= pc or join > stop then return nil end
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
    ["main.recover.functions"] = [===[local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local fn = {}

local evt = {
    PlayerAdded = { "player" }, PlayerRemoving = { "player" }, CharacterAdded = { "character" }, CharacterRemoving = { "character" },
    ChildAdded = { "child" }, ChildRemoved = { "child" }, DescendantAdded = { "descendant" }, DescendantRemoving = { "descendant" },
    Touched = { "hit" }, TouchEnded = { "hit" }, InputBegan = { "input", "gameProcessed" }, InputChanged = { "input", "gameProcessed" },
    InputEnded = { "input", "gameProcessed" }, Heartbeat = { "dt" }, RenderStepped = { "dt" }, PreRender = { "dt" },
    PreSimulation = { "dt" }, PostSimulation = { "dt" }, Stepped = { "time", "dt" }, AncestryChanged = { "child", "parent" },
    AttributeChanged = { "attribute" }, Changed = { "value" },
}
local meth = { BindToRenderStep = { "dt" }, BindAction = { "actionName", "inputState", "input" }, BindActionAtPriority = { "actionName", "inputState", "input" } }

local function cbhints(st, pc, r)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local call
    for _, u in ipairs(st.ir:uses(v) or {}) do if u.pc then if call then return nil end; call = u.pc end end
    if not call then return nil end
    local op = st.proto.Instructions[call]
    local name = ins.name(op)
    if name ~= "CALL" and name ~= "CALLFB" then return nil end
    local pend = st.namecall[op.A]
    if pend and (pend.method == "Connect" or pend.method == "ConnectParallel" or pend.method == "Once") then
        local tail = pend.obj and pend.obj:match("([%a_][%w_]*)$")
        return tail and evt[tail] or nil
    end
    return pend and meth[pend.method] or nil
end

local function capturename(st, cp, kind, src, debugname)


    local parent
    if kind == 0 or kind == 1 then
        parent = st:useName(cp, src, nil)
    else
        parent = st.up[src + 1] or ("upvalue" .. tostring(src))
    end
    if not parent or parent == "" then parent = debugname end
    return parent or ("upvalue" .. tostring(src))
end

function fn.caps(st, pc, child)
    local out = {}
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        local du = child.Upvalues and child.Upvalues[i]
        local dn = du and du.Name
        if not op or ins.name(op) ~= "CAPTURE" then
            error(("LumenV4: UNSUPPORTED NEWCLOSURE at pc %d expected CAPTURE %d/%d"):format(pc, i, child.UpvalueCount or 0), 2)
        end

        local kind, src = op.A, op.B
        if kind ~= 0 and kind ~= 1 and kind ~= 2 then
            error(("LumenV4: UNSUPPORTED CAPTURE kind %s at pc %d"):format(tostring(kind), cp), 2)
        end
        if kind == 0 or kind == 1 then
            if not st:veruse(cp, src) then
                error(("LumenV4: UNSUPPORTED CAPTURE references undefined parent register R%d at pc %d"):format(src, cp), 2)
            end
        elseif not st.up[src + 1] then
            error(("LumenV4: UNSUPPORTED CAPTURE_UPVAL references missing parent upvalue U%d at pc %d"):format(src, cp), 2)
        end

        if kind == 0 then


            local snap = st.naming:unique("capture" .. tostring(i) .. "Value")
            st.declared[snap] = st.indent
            st:out("local " .. snap .. " = " .. st:use(cp, src))
            out[i] = snap
        else
            out[i] = capturename(st, cp, kind, src, dn)
        end
        st.consumed[cp] = true
        nx = st:next(cp)
    end
    local extra = st.proto.Instructions[nx]
    if extra and ins.name(extra) == "CAPTURE" then
        error(("LumenV4: UNSUPPORTED NEWCLOSURE at pc %d has more CAPTURE instructions than child upvalues"):format(pc), 2)
    end
    return out, nx
end

local function direct(st, pc, r, nx)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local uses, one = st.ir:uses(v) or {}, nil
    for _, u in ipairs(uses) do if u.pc then if one then return nil end; one = u end end
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
        if not assign and target:find("%.") and args[1] and (args[1]:match("^self%s*[:$]") or args[1] == "self") then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then target = base .. ":" .. field; table.remove(args, 1) end
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
    assert(type(getscriptbytecode) == "function", "LumenDecomp: executor does not expose getscriptbytecode()")
    local ok, raw = pcall(getscriptbytecode, obj)
    if not ok then error("LumenDecomp: getscriptbytecode failed: " .. tostring(raw), 2) end
    local ty = typeof(raw)
    assert(type(raw) == "string" or ty == "buffer", "LumenDecomp: getscriptbytecode returned unsupported type " .. tostring(ty))
    if type(raw) == "string" then
        assert(#raw > 0, "LumenDecomp: getscriptbytecode returned empty bytecode")
    elseif ty == "buffer" then
        assert(buffer.len(raw) > 0, "LumenDecomp: getscriptbytecode returned empty bytecode")
    end
    return raw
end

function bc.try(obj)
    local ok, raw = pcall(bc.fromScript, obj)
    if ok then return true, raw end
    return false, tostring(raw)
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

local paths = {
    "Src/init.luau",
    "Src/Deserializer.d.luau",
    "Src/Utilities/Buffer.luau",
    "Src/Luau/Spec.luau",
    "Src/Luau/TypeInfo.luau",
    "Src/Classes/Proto.luau",
    "Src/Classes/Instructions.luau",
    "Src/Classes/Instruction.luau",
    "Src/Classes/Hexadecimal.luau",
    "Src/Classes/Upvalue.luau",
    "Src/Classes/Constants/Nil.luau",
    "Src/Classes/Constants/Boolean.luau",
    "Src/Classes/Constants/Number.luau",
    "Src/Classes/Constants/String.luau",
    "Src/Classes/Constants/Import.luau",
    "Src/Classes/Constants/Table.luau",
    "Src/Classes/Constants/Closure.luau",
    "Src/Classes/Constants/Vector.luau",
    "Src/Classes/Constants/TableWithConstants.luau",
    "Src/Classes/Constants/Integer.luau",
    "Src/Classes/Constants/ClassShape.luau",
}

local cache = {}
local srcs = {}
local NIL = {}
local LOADING = {}
local root = nil
local loading = false
local loaderr = nil
local warming = false
local warmed = false
local warmerr = nil

local e = env.get()
local vend = rawget(e, "__LUMEN_IRIDIUM_VENDOR")
if type(vend) == "table" then
    for k, v in pairs(vend) do
        if type(k) == "string" and type(v) == "string" then srcs[k] = v end
    end
end

local function resolve(name)
    if name == "@root" then return "Src/init.luau" end
    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end
    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local function fetch(path)
    local src = srcs[path]
    if src then return src end
    src = http.get(rawBase .. path)
    srcs[path] = src
    return src
end

function iri.prefetch()
    if warmed then return true end
    if warming then
        while warming do task.wait() end
        if warmerr then return false, warmerr end
        return true
    end

    warming = true
    warmerr = nil
    local left = 0
    local errs = {}

    for _, path in ipairs(paths) do
        if not srcs[path] then
            left += 1
            task.spawn(function()
                local ok, val = pcall(http.get, rawBase .. path)
                if ok and type(val) == "string" and val ~= "" then
                    srcs[path] = val
                else
                    errs[#errs + 1] = path .. ": " .. tostring(val)
                end
                left -= 1
            end)
        end
    end

    while left > 0 do task.wait() end
    warming = false
    if #errs > 0 then
        warmerr = table.concat(errs, " | ")
        return false, warmerr
    end
    warmed = true
    return true
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
        local src = patch.apply(path, fetch(path))
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
    if root then return root end
    if loading then
        while loading do task.wait() end
        if root then return root end
        error(loaderr or "LumenDecomp: Iridium load failed", 2)
    end

    loading = true
    loaderr = nil
    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)
    e[key] = req
    local ok, value = pcall(req, "@root")
    if old == nil then e[key] = nil else e[key] = old end

    if not ok then
        loading = false
        loaderr = tostring(value)
        error(value, 2)
    end

    if type(value) ~= "table" or type(value.Deserialize) ~= "function" then
        loading = false
        loaderr = "LumenDecomp: Iridium root did not expose Deserialize"
        error(loaderr, 2)
    end

    root = value
    loading = false
    return root
end

function iri.warm()
    iri.prefetch()
    local rok, val = pcall(iri.get)
    if not rok then return false, tostring(val) end
    return true
end

local function lit(s)
    for n = 3, 12 do
        local eq = string.rep("=", n)
        local close = "]" .. eq .. "]"
        if not s:find(close, 1, true) then
            return "[" .. eq .. "[" .. s .. close
        end
    end
    return string.format("%q", s)
end

function iri.pack()
    iri.prefetch()
    for _, path in ipairs(paths) do
        if not srcs[path] then
            local ok, val = pcall(fetch, path)
            if not ok then return nil, tostring(val) end
        end
    end
    local out = { "return {" }
    for _, path in ipairs(paths) do
        out[#out + 1] = "[" .. string.format("%q", path) .. "]=" .. lit(srcs[path]) .. ","
    end
    out[#out + 1] = "}"
    return table.concat(out)
end

function iri.info()
    local pi = patch.info()
    local n = 0
    for _ in pairs(srcs) do n += 1 end
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
        prefetched = n,
        vendor = type(vend) == "table",
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
		local slice = os.clock()
		local spins = 0
		local function pulse(force)
			spins = spins + 1
			if force or spins >= 64 then
				spins = 0
				local now = os.clock()
				if force or now - slice >= 0.004 then
					task.wait()
					slice = os.clock()
				end
			end
		end

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
		pulse(true)

		-- Count instances and instance types
		local function recur(obj)
			pulse()
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
				pulse()
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
				pulse()
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
				pulse()
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
				pulse()
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

			pulse(true)
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
				pulse()
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

					pulse(true)
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
				pulse()
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
				pulse()
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
		pulse(true)


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
    ["main.tree"] = [===[
local tree = {}

local win = {
    CON = true, PRN = true, AUX = true, NUL = true,
    COM1 = true, COM2 = true, COM3 = true, COM4 = true, COM5 = true,
    COM6 = true, COM7 = true, COM8 = true, COM9 = true,
    LPT1 = true, LPT2 = true, LPT3 = true, LPT4 = true, LPT5 = true,
    LPT6 = true, LPT7 = true, LPT8 = true, LPT9 = true,
}

local cls = { LocalScript = true, ModuleScript = true, Script = true }

local function hash(s)
    local h = 7
    for i = 1, #s do
        h = (h * 131 + s:byte(i)) % 2147483647
    end
    return string.format("%08x", h)
end

local function clean(s)
    s = tostring(s or "")
    s = s:gsub("[%z\1-\31]", "_")
    s = s:gsub('[<>:"/\\|%?%*]', "_")
    s = s:gsub("[%.%s]+$", "")
    if s == "" then s = "_unnamed" end
    local b = s:match("^([^%.]+)") or s
    if win[b:upper()] then s = "_" .. s end
    if #s > 80 then s = s:sub(1, 71) .. "_" .. hash(s) end
    return s
end

local function kids(obj)
    local ok, out = pcall(obj.GetChildren, obj)
    if not ok or type(out) ~= "table" then return nil, out end
    return out
end

local function iscript(obj)
    local ok, c = pcall(function() return obj.ClassName end)
    return ok and cls[c] == true
end

local function mk(path, made)
    if made[path] then return true end
    if type(isfolder) == "function" then
        local ok, yes = pcall(isfolder, path)
        if ok and yes then
            made[path] = true
            return true
        end
    end
    if type(makefolder) ~= "function" then return false end
    local ok = pcall(makefolder, path)
    if ok then made[path] = true end
    return ok
end

local function mkall(path, made)
    local cur = ""
    for p in tostring(path):gmatch("[^/]+") do
        cur = cur == "" and p or cur .. "/" .. p
        if not mk(cur, made) then return false end
    end
    return true
end

local function extname(s)
    local low = s:lower()
    if low:sub(-5) == ".luau" or low:sub(-4) == ".lua" then return s end
    return s .. ".luau"
end

local function numbered(s, n)
    local stem, ext = s:match("^(.*)(%.luau)$")
    if not stem then stem, ext = s:match("^(.*)(%.lua)$") end
    if not stem then return s .. "__" .. tostring(n) end
    return stem .. "__" .. tostring(n) .. ext
end

local function build(parent, ctx)
    local hit = ctx.idx[parent]
    if hit then return hit end
    local list, err = kids(parent)
    local out = { seg = {}, file = {}, err = err }
    ctx.idx[parent] = out
    if not list then return out end

    local seen = {}
    for _, obj in ipairs(list) do
        if ctx.dirinst[obj] then
            local base = clean(obj.Name)
            local key = base:lower()
            local n = (seen[key] or 0) + 1
            seen[key] = n
            out.seg[obj] = n == 1 and base or base .. "__" .. tostring(n)
        end
    end

    local used = {}
    for _, name in pairs(out.seg) do used[name:lower()] = true end
    for _, obj in ipairs(list) do
        if ctx.scriptset[obj] then
            local base = extname(clean(obj.Name))
            local name = base
            local n = 2
            while used[name:lower()] do
                name = numbered(base, n)
                n = n + 1
            end
            used[name:lower()] = true
            out.file[obj] = name
        end
    end
    return out
end

local function seg(obj, ctx)
    local p = obj and obj.Parent
    if not p then return clean(obj and obj.Name) end
    local x = build(p, ctx)
    return x.seg[obj] or clean(obj.Name)
end

local function file(obj, ctx)
    local p = obj.Parent
    if p then
        local x = build(p, ctx)
        if x.file[obj] then return x.file[obj] end
    end
    return extname(clean(obj.Name))
end

local function rel(obj, ctx)
    local rev = {}
    local cur = obj.Parent
    while cur and cur ~= game do
        rev[#rev + 1] = seg(cur, ctx)
        cur = cur.Parent
    end
    local out = {}
    for i = #rev, 1, -1 do out[#out + 1] = rev[i] end
    return out
end

local function flat(obj, ctx)
    local p = rel(obj, ctx)
    p[#p + 1] = file(obj, ctx)
    return table.concat(p, "__")
end

local function short(ctx, path, name)
    if #path <= ctx.max then return path end
    local dir = ctx.root .. "/_LongPaths"
    mkall(dir, ctx.made)
    local stem, ext = name:match("^(.*)(%.luau)$")
    if not stem then stem, ext = name:match("^(.*)(%.lua)$") end
    stem = stem or name
    ext = ext or ".luau"
    local n = stem:sub(1, 50) .. "_" .. hash(path) .. ext
    return dir .. "/" .. n
end

local function full(obj)
    local ok, s = pcall(obj.GetFullName, obj)
    if ok and type(s) == "string" then return s end
    return tostring(obj.Name)
end

local function one(s)
    return tostring(s or ""):gsub("[\r\n\t]", " ")
end

function tree.new(root, made, max, list)
    local ctx = {
        root = root,
        made = made or {},
        max = tonumber(max) or 240,
        idx = {},
        map = {},
        dirinst = {},
        scriptset = {},
    }
    for _, obj in ipairs(list or {}) do
        ctx.scriptset[obj] = true
        local cur = obj.Parent
        while cur and cur ~= game do
            ctx.dirinst[cur] = true
            cur = cur.Parent
        end
    end
    return ctx
end

function tree.path(ctx, obj, treeon)
    local dir = ctx.root
    local name
    if treeon then
        local p = rel(obj, ctx)
        if #p > 0 then dir = dir .. "/" .. table.concat(p, "/") end
        name = file(obj, ctx)
    else
        dir = ctx.root .. "/Scripts"
        name = flat(obj, ctx)
    end
    mkall(dir, ctx.made)
    return short(ctx, dir .. "/" .. name, name)
end

function tree.record(ctx, obj, path, state)
    ctx.map[#ctx.map + 1] = table.concat({
        one(state), one(obj.ClassName), one(full(obj)), one(path)
    }, "\t")
end

function tree.map(ctx)
    local out = { "status\tclass\troblox_path\tfile" }
    for _, line in ipairs(ctx.map) do out[#out + 1] = line end
    return table.concat(out, "\n")
end

function tree.placeholder(obj, v)
    local state = v and v.unavailable and "source unavailable" or "decompile failed"
    local reason = one(v and v.error or "unknown error")
    return "-- LumenDecomp: " .. state .. "\n-- Path: " .. one(full(obj)) .. "\n-- Class: " .. one(obj.ClassName) .. "\n-- Reason: " .. reason .. "\n"
end

function tree.scan(ignore, core)
    local out = {}
    local errors = {}
    local roots, err = kids(game)
    if not roots then return out, { "game :: " .. tostring(err) } end
    local stack = {}
    for i = #roots, 1, -1 do stack[#stack + 1] = roots[i] end

    while #stack > 0 do
        local obj = stack[#stack]
        stack[#stack] = nil
        local skip = false
        if ignore and core then
            local ok, yes = pcall(core.is, obj)
            skip = ok and yes == true
        end
        if not skip then
            if iscript(obj) then out[#out + 1] = obj end
            local list, e = kids(obj)
            if list then
                for i = #list, 1, -1 do stack[#stack + 1] = list[i] end
            else
                errors[#errors + 1] = full(obj) .. " :: " .. tostring(e)
            end
        end
    end
    return out, errors
end

function tree.mkall(path, made)
    return mkall(path, made)
end

function tree.clean(s)
    return clean(s)
end

function tree.script(obj)
    return iscript(obj)
end

return tree
]===],
    ["main.version"] = [===[return { name = "LumenDecomp", version = "4.0.0" }
]===],
    ["main.worker"] = [===[
local cfg = require("main.config")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:warm()
    local ok, err = iri.warm()
    if not ok then error(err, 2) end
    return true
end

function worker:decompileBytecode(raw, opt)
    opt = cfg(opt)
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

function dom.compute(blocks, check)
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
        if check then check() end
        chg = false

        for _, block in ipairs(blocks) do
            if check then check() end
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
    ["main.analysis.graph"] = [===[local ins = require("main.bytecode.instructions")
local regs = require("main.analysis.registers")
local dom = require("main.analysis.dominators")
local loops = require("main.analysis.loops")
local post = require("main.analysis.postdom")

local graph = {}

local function immediatefromsets(blocks, sets, check)
    local out = {}
    for _, b in ipairs(blocks) do
        if check then check() end
        local cand = {}
        for id in pairs(sets[b.id] or {}) do if id ~= b.id then cand[#cand + 1] = id end end
        table.sort(cand)
        for _, id in ipairs(cand) do
            local immediate = true
            for _, other in ipairs(cand) do
                if other ~= id and sets[other] and sets[other][id] then immediate = false break end
            end
            if immediate then out[b.id] = id break end
        end
    end
    return out
end

local function dominancefrontiers(blocks, idom, check)
    local df = {}; for _, b in ipairs(blocks) do df[b.id] = {} end
    for _, b in ipairs(blocks) do
        if check then check() end
        if #b.predecessors >= 2 then
            for _, pred in ipairs(b.predecessors) do
                local runner = pred
                local guard = {}
                while runner and runner ~= idom[b.id] and not guard[runner] do
                    guard[runner] = true
                    df[runner][b.id] = true
                    runner = idom[runner]
                end
            end
        end
    end
    return df
end

local function tarjan(blocks, check)
    local index, stack, onstack, idx, low, out = 0, {}, {}, {}, {}, {}
    local function visit(v)
        if check then check() end
        index += 1; idx[v] = index; low[v] = index; stack[#stack + 1] = v; onstack[v] = true
        for _, w in ipairs(blocks[v].successors) do
            if not idx[w] then visit(w); low[v] = math.min(low[v], low[w])
            elseif onstack[w] then low[v] = math.min(low[v], idx[w]) end
        end
        if low[v] == idx[v] then
            local nodes, set = {}, {}
            while true do
                local w = stack[#stack]; stack[#stack] = nil; onstack[w] = nil
                nodes[#nodes + 1] = w; set[w] = true
                if w == v then break end
            end
            table.sort(nodes)
            local cyclic = #nodes > 1
            if #nodes == 1 then for _, w in ipairs(blocks[nodes[1]].successors) do if w == nodes[1] then cyclic = true break end end end
            local entries, exits = {}, {}
            for _, n in ipairs(nodes) do
                for _, pred in ipairs(blocks[n].predecessors) do if not set[pred] then entries[n] = true end end
                for _, succ in ipairs(blocks[n].successors) do if not set[succ] then exits[succ] = true end end
            end
            local entrycount = 0; for _ in pairs(entries) do entrycount += 1 end
            out[#out + 1] = { nodes = nodes, set = set, cyclic = cyclic, entries = entries, exits = exits, irreducible = cyclic and entrycount > 1 }
        end
    end
    for _, b in ipairs(blocks) do if not idx[b.id] then visit(b.id) end end
    table.sort(out, function(a,b) return a.nodes[1] < b.nodes[1] end)
    return out
end

local function loopforest(natural, check)
    local parent = {}
    local function subset(a, b)
        for id in pairs(a) do if not b[id] then return false end end
        return true
    end
    for i, loop in ipairs(natural) do
        if check then check() end
        local best, bestsize
        local size = 0; for _ in pairs(loop.nodes) do size += 1 end
        for j, outer in ipairs(natural) do
            if i ~= j and subset(loop.nodes, outer.nodes) then
                local os = 0; for _ in pairs(outer.nodes) do os += 1 end
                if os > size and (not bestsize or os < bestsize) then best, bestsize = j, os end
            end
        end
        parent[i] = best
    end
    return parent
end

local function push(t, v)
    for _, x in ipairs(t) do if x == v then return end end
    t[#t + 1] = v
end

local function edgesuccessors(proto, pc, aux)
    local op = proto.Instructions[pc]
    local name = ins.name(op)
    local nx = ins.next(proto, pc, aux)
    local out = {}

    local function valid(p)
        return p >= 1 and p <= #proto.Instructions and not aux[p]
    end
    local function add(p)
        if valid(p) then push(out, p) end
    end

    if name == "RETURN" then
        return out
    elseif name == "LOADB" and (op.C or 0) ~= 0 then
        add(pc + (op.C or 0) + 1)
    elseif name == "FORNPREP" then

        add(nx)
        add(ins.jumpTarget(pc, op))
    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then

        add(ins.jumpTarget(pc, op))
    elseif ins.isConditional(op) then
        add(ins.jumpTarget(pc, op))
        add(nx)
    elseif ins.isUnconditional(op) then
        add(ins.jumpTarget(pc, op))
    else
        add(nx)
    end
    return out
end

local function verify(proto, aux, blocks, blockmap, nexts)
    local covered = {}
    for _, b in ipairs(blocks) do
        assert(b.id >= 1 and b.id <= #blocks, "LumenV4: CFG block id out of range")
        assert(#b.pcs > 0, "LumenV4: empty CFG block")
        for _, pc in ipairs(b.pcs) do
            assert(not aux[pc], "LumenV4: AUX word entered a basic block")
            assert(not covered[pc], "LumenV4: duplicate CFG PC " .. tostring(pc))
            covered[pc] = b.id
            assert(blockmap[pc] == b.id, "LumenV4: blockmap mismatch at PC " .. tostring(pc))
        end
        for _, sid in ipairs(b.successors) do
            assert(blocks[sid], "LumenV4: invalid CFG successor " .. tostring(sid))
            local back = false
            for _, pid in ipairs(blocks[sid].predecessors) do if pid == b.id then back = true break end end
            assert(back, "LumenV4: asymmetric CFG edge")
        end
    end
    for pc = 1, #proto.Instructions do
        if not aux[pc] and blockmap[pc] then
            for _, target in ipairs(nexts[pc] or {}) do
                assert(blockmap[target], "LumenV4: successor has no block at PC " .. tostring(target))
            end
        end
    end
    return true
end

function graph.build(proto, check, limits)
    local ops = proto.Instructions
    limits = limits or {}
    local maxinstructions = tonumber(limits.maxinstructions) or 0
    local maxblocks = tonumber(limits.maxblocks) or 0
    if maxinstructions > 0 and #ops > maxinstructions then
        error("LumenV4: STRUCTURED_COMPLEXITY proto instructions " .. tostring(#ops) .. " > " .. tostring(maxinstructions), 2)
    end
    if check then check() end
    local aux = ins.auxSlots(proto)
    local leaders = { [1] = true }
    local nexts = {}

    local function valid(pc)
        return pc >= 1 and pc <= #ops and not aux[pc]
    end

    for pc = 1, #ops do
        if not aux[pc] then
            local successors = edgesuccessors(proto, pc, aux)
            nexts[pc] = successors
            for _, target in ipairs(successors) do leaders[target] = true end

            local op = ops[pc]
            local name = ins.name(op)
            local nx = ins.next(proto, pc, aux)

            if name == "RETURN" or name == "LOADB" and (op.C or 0) ~= 0
                or name == "FORNPREP" or ins.isConditional(op) or ins.isUnconditional(op) then
                if valid(nx) then leaders[nx] = true end
            end
        end
    end

    local list = {}
    for pc in pairs(leaders) do if valid(pc) then list[#list + 1] = pc end end
    table.sort(list)

    local rawblocks, rawmap = {}, {}
    for index, startpc in ipairs(list) do
        local nextleader = list[index + 1] or (#ops + 1)
        local pcs = {}
        for pc = startpc, nextleader - 1 do
            if not aux[pc] then
                pcs[#pcs + 1] = pc
                rawmap[pc] = index
            end
        end
        if #pcs > 0 then
            rawblocks[index] = { id = index, startPC = startpc, endPC = pcs[#pcs], pcs = pcs, successors = {}, predecessors = {} }
        end
    end

    for _, b in ipairs(rawblocks) do
        for _, target in ipairs(nexts[b.endPC] or {}) do
            local sid = rawmap[target]
            if sid then push(b.successors, sid) end
        end
    end


    local reachable, todo = {}, { rawmap[1] }
    local at = 1
    while at <= #todo do
        local id = todo[at]; at += 1
        if id and not reachable[id] then
            reachable[id] = true
            for _, sid in ipairs(rawblocks[id].successors) do todo[#todo + 1] = sid end
        end
    end

    local remap, blocks = {}, {}
    for oldid, b in ipairs(rawblocks) do
        if reachable[oldid] then
            local id = #blocks + 1
            remap[oldid] = id
            blocks[id] = { id = id, startPC = b.startPC, endPC = b.endPC, pcs = b.pcs, successors = {}, predecessors = {} }
        end
    end

    local blockmap = {}
    for oldid, newid in pairs(remap) do
        local old = rawblocks[oldid]
        local b = blocks[newid]
        for _, pc in ipairs(b.pcs) do blockmap[pc] = newid end
        for _, oldsucc in ipairs(old.successors) do
            local sid = remap[oldsucc]
            if sid then push(b.successors, sid) end
        end
    end
    for _, b in ipairs(blocks) do
        for _, sid in ipairs(b.successors) do push(blocks[sid].predecessors, b.id) end
    end

    if maxblocks > 0 and #blocks > maxblocks then
        error("LumenV4: STRUCTURED_COMPLEXITY cfg blocks " .. tostring(#blocks) .. " > " .. tostring(maxblocks), 2)
    end
    if check then check() end
    local dominators = dom.compute(blocks, check)
    local idom = immediatefromsets(blocks, dominators, check)
    local postdom, ipdom, exitid = post.run(blocks, check)
    local naturalloops = loops.find(blocks, dominators, check)
    local sccs = tarjan(blocks, check)
    local out = {
        proto = proto,
        aux = aux,
        blocks = blocks,
        blockmap = blockmap,
        nexts = nexts,
        dominators = dominators,
        idom = idom,
        dominanceFrontiers = dominancefrontiers(blocks, idom, check),
        postdom = postdom,
        ipdom = ipdom,
        exitId = exitid,
        loops = naturalloops,
        loopForest = loopforest(naturalloops, check),
        sccs = sccs,
        irreducible = false,
        registerStats = regs.stats(proto, aux),
    }
    for _, component in ipairs(sccs) do if component.irreducible then out.irreducible = true break end end
    out.verified = verify(proto, aux, blocks, blockmap, nexts)
    return out
end

return graph
]===],
    ["main.analysis.loops"] = [===[
local loops = {}

function loops.find(blocks, dom, check)
    local out = {}

    for _, latch in ipairs(blocks) do
        if check then check() end
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

local function clone(s)
    local out = {}
    for k in pairs(s) do out[k] = true end
    return out
end

local function same(a, b)
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end

local function intersectinto(dst, src)
    for k in pairs(dst) do
        if not src[k] then dst[k] = nil end
    end
end

function post.run(blocks, check)
    local exitid = #blocks + 1
    local all = { [exitid] = true }
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = { [exitid] = { [exitid] = true } }
    for _, b in ipairs(blocks) do pd[b.id] = clone(all) end

    local dirty = true
    local iterations = 0
    local limit = math.max(64, (#blocks + 1) * (#blocks + 1) * 4)
    while dirty do
        if check then check() end
        iterations += 1
        if iterations > limit then
            error("LumenV4: post-dominator analysis failed to converge", 2)
        end
        dirty = false

        for i = #blocks, 1, -1 do
            local b = blocks[i]
            local succ = b.successors
            local set

            if #succ == 0 then
                set = clone(pd[exitid])
            else
                for _, sid in ipairs(succ) do
                    local src = assert(pd[sid], "LumenV4: invalid postdom successor " .. tostring(sid))
                    if not set then set = clone(src) else intersectinto(set, src) end
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

    local ip = {}
    for _, b in ipairs(blocks) do
        if check then check() end
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        table.sort(cand)

        for _, id in ipairs(cand) do
            local immediate = true

            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    immediate = false
                    break
                end
            end
            if immediate then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip, exitid
end

return post
]===],
    ["main.analysis.registers"] = [===[local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then set[value] = true end
end
local function range(set, first, last)
    for reg = first, math.min(last, 254) do add(set, reg) end
end


function regs.readWrite(op)
    local reads, writes, pack = {}, {}, {}
    local name = ins.name(op)
    local ra, rb, rc = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL" or name == "GETIMPORT"
        or name == "NEWTABLE" or name == "DUPTABLE" or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, ra)
    elseif name == "MOVE" then add(reads, rb); add(writes, ra)
    elseif name == "SETGLOBAL" or name == "SETUPVAL" then add(reads, ra)
    elseif name == "GETTABLE" then add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "SETTABLE" then add(reads, ra); add(reads, rb); add(reads, rc)
    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then add(reads, rb); add(writes, ra)
    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then add(reads, ra); add(reads, rb)
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then add(reads, rb); add(writes, ra); add(writes, ra + 1)
    elseif name == "CALL" or name == "CALLFB" then
        add(reads, ra)
        if rb == 0 then
            pack.openReadFrom = ra + 1
            pack.consumesTop = true
        elseif rb > 1 then range(reads, ra + 1, ra + rb - 1) end
        if rc == 0 then
            add(writes, ra)
            pack.openWriteFrom = ra
            pack.producesTop = true
        elseif rc > 1 then range(writes, ra, ra + rc - 2) end
    elseif name == "RETURN" then
        if rb == 0 then add(reads, ra); pack.openReadFrom = ra; pack.consumesTop = true
        elseif rb > 1 then range(reads, ra, ra + rb - 2) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        add(reads, rb); add(writes, ra)
    elseif name == "SUBRK" or name == "DIVRK" then add(reads, rc); add(writes, ra)
    elseif name == "CONCAT" then range(reads, rb, rc); add(writes, ra)
    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then add(reads, rb); add(writes, ra)
    elseif name == "SETLIST" then
        add(reads, ra)
        if rc == 0 then add(reads, rb); pack.openReadFrom = rb; pack.consumesTop = true
        elseif rc > 1 then range(reads, rb, rb + rc - 2) end
    elseif name == "FORNPREP" then
        range(reads, ra, ra + 2)


        range(writes, ra, ra + 2)
    elseif name == "FORNLOOP" then
        range(reads, ra, ra + 2); add(writes, ra + 2)
    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, ra, ra + 2); range(writes, ra, ra + 2)
    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, ra, ra + 2); add(writes, ra + 2)
        if count > 0 then range(writes, ra + 3, ra + 2 + count) end
    elseif name == "GETVARARGS" then
        if rb == 0 then add(writes, ra); pack.openWriteFrom = ra; pack.producesTop = true
        elseif rb > 1 then range(writes, ra, ra + rb - 2) end
    elseif name == "CAPTURE" then if ra == 0 or ra == 1 then add(reads, rb) end
    elseif name == "JUMPIF" or name == "JUMPIFNOT" or name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" or name == "CMPPROTO" then
        add(reads, ra)
    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, ra); add(reads, bit32.band(aux, 0xff))
    elseif name == "NEWCLASSMEMBER" then add(reads, ra); add(reads, rc)
    elseif name == "NEWCLASS" then if rb ~= 0xff then add(reads, rb) end; add(writes, ra)
    end

    return reads, writes, pack
end

function regs.stats(proto, aux)
    local stats = {}
    aux = aux or ins.auxSlots(proto)
    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = { reads = 0, writes = 0, firstWrite = nil, lastWrite = nil, firstRead = nil, lastRead = nil, firstAccess = nil, lastAccess = nil }
            stats[reg] = entry
        end
        return entry
    end
    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local reads, writes = regs.readWrite(proto.Instructions[pc])
            for reg in pairs(reads) do
                local e = get(reg); e.reads += 1; e.firstRead = e.firstRead or pc; e.lastRead = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
            end
            local name = ins.name(proto.Instructions[pc])
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local e = get(reg); e.writes += 1; e.firstWrite = e.firstWrite or pc; e.lastWrite = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
                end
            end
        end
    end
    return stats
end

return regs
]===],
    ["main.analysis.ssa"] = [===[local graph = require("main.analysis.graph")
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
    ["main.ast.doblocks"] = [===[
local pass = {}

local function words(s, out)
    if type(s) ~= "string" then return end
    for x in s:gmatch("[%a_][%w_]*") do out[x] = true end
end

local function declraw(s)
    if type(s) ~= "string" then return {} end
    local head = s:match("^local%s+(.+)$")
    if not head or head:match("^function%s") then return {} end
    head = head:match("^(.-)%s*=") or head
    local out = {}
    for part in head:gmatch("[^,]+") do
        local name = part:match("^%s*([%a_][%w_]*)")
        if name then out[#out + 1] = name end
    end
    return out
end

local function decls(n)
    if n.kind == "raw" then return declraw(n.text) end
    if n.kind == "function" and n.localfn then return { n.name } end
    return {}
end

local function scanblock(b, out)
    for _, n in ipairs(b.body or {}) do
        if not n.dead then
            if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
                words(n.text, out)
            elseif n.kind == "if" then
                for _, x in ipairs(n.branches or {}) do
                    words(x.cond, out)
                    scanblock(x.body, out)
                end
                if n.elsebody then scanblock(n.elsebody, out) end
            elseif n.kind == "while" or n.kind == "repeat" then
                words(n.cond, out)
                scanblock(n.body, out)
            elseif n.kind == "for" then
                words(n.head, out)
                scanblock(n.body, out)
            elseif n.kind == "do" then
                scanblock(n.body, out)
            elseif n.kind == "callback" then
                words(n.pre, out)
                words(n.args, out)
                words(n.post, out)
                scanblock(n.body, out)
            elseif n.kind == "function" then
                words(n.name, out)
                words(n.args, out)
                scanblock(n.body, out)
            end
        end
    end
end

local function refs(n)
    local out = {}
    if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
        words(n.text, out)
    elseif n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do
            words(x.cond, out)
            scanblock(x.body, out)
        end
        if n.elsebody then scanblock(n.elsebody, out) end
    elseif n.kind == "while" or n.kind == "repeat" then
        words(n.cond, out)
        scanblock(n.body, out)
    elseif n.kind == "for" then
        words(n.head, out)
        scanblock(n.body, out)
    elseif n.kind == "do" then
        scanblock(n.body, out)
    elseif n.kind == "callback" then
        words(n.pre, out)
        words(n.args, out)
        words(n.post, out)
        scanblock(n.body, out)
    elseif n.kind == "function" then
        words(n.name, out)
        words(n.args, out)
        scanblock(n.body, out)
    end
    for _, name in ipairs(decls(n)) do out[name] = nil end
    return out
end

local function children(n, threshold)
    if n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do pass.run(x.body, threshold) end
        if n.elsebody then pass.run(n.elsebody, threshold) end
    elseif n.body then
        pass.run(n.body, threshold)
    end
end

function pass.run(block, threshold)
    threshold = math.floor(tonumber(threshold) or 0)
    for _, n in ipairs(block.body or {}) do children(n, threshold) end
    if threshold <= 0 or #(block.body or {}) < 2 then return block end

    local body = block.body
    local used = {}
    for i, n in ipairs(body) do used[i] = refs(n) end

    local last = {}
    for i = #body, 1, -1 do
        for name in pairs(used[i]) do
            if last[name] == nil then last[name] = i end
        end
    end

    local ranges = {}
    local start = nil
    local count = 0
    local finish = 0
    for i, n in ipairs(body) do
        local ds = decls(n)
        if #ds > 0 then
            if not start then start = i end
            count += #ds
            for _, name in ipairs(ds) do
                local x = last[name] or i
                if x > finish then finish = x end
            end
        end
        if start and i >= finish and count >= threshold then
            ranges[#ranges + 1] = { start, i }
            start = nil
            count = 0
            finish = 0
        end
    end

    if #ranges == 0 then return block end
    local by = {}
    for _, r in ipairs(ranges) do by[r[1]] = r[2] end
    local out = {}
    local i = 1
    while i <= #body do
        local e = by[i]
        if e then
            local sub = { kind = "block", body = {} }
            for j = i, e do sub.body[#sub.body + 1] = body[j] end
            out[#out + 1] = { kind = "do", body = sub }
            i = e + 1
        else
            out[#out + 1] = body[i]
            i += 1
        end
    end
    block.body = out
    return block
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


local pass = {}

function pass.run(root, opt)
    return root
end

return pass
]===],
    ["main.ast.printer"] = [===[
local printast = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hasname(node, name)
    if not node or node.dead then return false end
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local function hit(s) return type(s) == "string" and s:find(pat) ~= nil end
    if hit(node.text) or hit(node.cond) or hit(node.head) or hit(node.args) then return true end
    if node.kind == "if" then
        for _, b in ipairs(node.branches or {}) do
            if hit(b.cond) then return true end
            for _, x in ipairs(b.body.body or {}) do if hasname(x, name) then return true end end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body or {}) do if hasname(x, name) then return true end end end
    elseif node.body then
        for _, x in ipairs(node.body.body or {}) do if hasname(x, name) then return true end end
    end
    return false
end

local function recursive(node)
    for _, x in ipairs(node.body.body or {}) do if hasname(x, node.name) then return true end end
    return false
end

local function indent(opt, depth)
    local n = tonumber(opt.formatter and opt.formatter.IndentWidth) or 4
    n = math.max(0, math.min(16, math.floor(n)))
    return string.rep(" ", n * depth)
end

local function line(out, opt, depth, s, stmt)
    if stmt and opt.formatter and opt.formatter.AppendSemicolons then
        local last = s:sub(-1)
        if last ~= ";" and last ~= ":" then s = s .. ";" end
    end
    out[#out + 1] = indent(opt, depth) .. s
end

local function cond(opt, s)
    if opt.formatter and opt.formatter.ParenthesizeConditions then return "(" .. s .. ")" end
    return s
end

local function fnhead(node, opt)
    local args = node.args or ""
    if opt.functions == false then
        if node.localfn then return "local " .. node.name .. " = function(" .. args .. ")" end
        if node.assign then return node.name .. " = function(" .. args .. ")" end
        local base, field = node.name:match("^(.*):([%a_][%w_]*)$")
        if base and field then
            local a = args ~= "" and ("self, " .. args) or "self"
            return base .. "." .. field .. " = function(" .. a .. ")"
        end
        return node.name .. " = function(" .. args .. ")"
    end
    if node.localfn then return "local function " .. node.name .. "(" .. args .. ")" end
    if node.assign then return node.name .. " = function(" .. args .. ")" end
    return "function " .. node.name .. "(" .. args .. ")"
end

local function block(out, b, depth, opt)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, opt, depth, node.text, true)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, opt, depth, (i == 1 and "if " or "elseif ") .. cond(opt, branch.cond) .. " then")
                    block(out, branch.body, depth + 1, opt)
                end
                if node.elsebody then
                    line(out, opt, depth, "else")
                    block(out, node.elsebody, depth + 1, opt)
                end
                line(out, opt, depth, "end")
            elseif k == "while" then
                line(out, opt, depth, "while " .. cond(opt, node.cond) .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "repeat" then
                line(out, opt, depth, "repeat")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "until " .. cond(opt, node.cond))
            elseif k == "for" then
                line(out, opt, depth, node.head .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "do" then
                line(out, opt, depth, "do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "callback" then
                line(out, opt, depth, node.pre .. "function(" .. node.args .. ")")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end" .. node.post, true)
            elseif k == "function" then
                if opt.functions == false and node.localfn and recursive(node) then
                    line(out, opt, depth, "local " .. node.name, true)
                    line(out, opt, depth, node.name .. " = function(" .. (node.args or "") .. ")")
                else
                    line(out, opt, depth, fnhead(node, opt))
                end
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end", opt.functions == false or node.assign)
            end
        end
    end
end

function printast.run(root, opt)
    opt = opt or {}
    local out = {}
    block(out, root, 0, opt)
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
    guards = false,
    types = true,
    selects = false,
    returns = false,
    compound = false,
    inlineast = false,
    callbacks = false,
    booleans = false,
    smartnames = true,
    functions = true,
    doblocks = 0,
    iridium = nil,
    fidelity = true,
    structuredbudget = 1.25,
    structuredmaxinstructions = 8000,
    structuredmaxprotoinstructions = 4000,
    structuredmaxblocks = 256,
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
    FidelityMode = "fidelity",
    StructuredBudgetSeconds = "structuredbudget",
    StructuredMaxInstructions = "structuredmaxinstructions",
    StructuredMaxProtoInstructions = "structuredmaxprotoinstructions",
    StructuredMaxBlocks = "structuredmaxblocks",
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[map[k] or k] = v end end
    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    out.structuredbudget = math.max(0, tonumber(out.structuredbudget) or 1.25)
    out.structuredmaxinstructions = math.max(0, math.floor(tonumber(out.structuredmaxinstructions) or 8000))
    out.structuredmaxprotoinstructions = math.max(0, math.floor(tonumber(out.structuredmaxprotoinstructions) or 4000))
    out.structuredmaxblocks = math.max(0, math.floor(tonumber(out.structuredmaxblocks) or 256))
    if out.fidelity ~= false then

        out.fold = false
        out.guards = false
        out.selects = false
        out.returns = false
        out.compound = false
        out.inlineast = false
        out.callbacks = false
        out.booleans = false
        out.doblocks = 0
    end
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

    if self.opt.smartnames == false then
        if di then
            name = self.naming:nameAt(r, pc, nil)
        elseif src and src.kind == "param" then
            name = self.naming:unique("arg" .. tostring(src.reg + 1))
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
    ["main.decompiler.engine"] = [===[local irbuild = require("main.ir.build")
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
local lit = require("main.output.literals")
local regs = require("main.analysis.registers")
local vmfallback = (function()
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local vm = {}

local function line(out, depth, text)
    out[#out + 1] = string.rep("    ", depth) .. text
end

local function key2(proto, index)
    return proto.Constants and proto.Constants[(index or 0) + 1]
end

local function rawstr(constant)
    return lit.rawStringConstant(constant)
end

local function q(value)
    return lit.string(tostring(value or ""))
end

local function classshapeexpr(k)
    local name = rawstr(k and k.ClassName) or "AnonymousClass"
    local props, methods = {}, {}
    for _, v in ipairs(k and k.Properties or {}) do props[#props + 1] = q(rawstr(v) or "property") end
    for _, v in ipairs(k and k.Methods or {}) do methods[#methods + 1] = q(rawstr(v) or "method") end
    return "__classshape(" .. q(name) .. ", {" .. table.concat(props, ", ") .. "}, {" .. table.concat(methods, ", ") .. "})"
end

local function constexpr(proto, index)
    local k = key2(proto, index)
    if not k then return "nil" end
    if k.__type == "Import" then
        local parts = {}
        for _, part in ipairs(k.Value or {}) do parts[#parts + 1] = rawstr(part) or "?" end
        if #parts == 0 then return "nil" end
        local first = parts[1]
        local out
        if first == "type" and #parts == 1 then out = "__v4type"
        elseif first == "typeof" and #parts == 1 then out = "__v4typeof"
        elseif first == "class" then out = "__classlib"
        else out = "__env[" .. q(first) .. "]" end
        for i = 2, #parts do out = out .. "[" .. q(parts[i]) .. "]" end
        return out
    elseif k.__type == "ClassShape" then
        return classshapeexpr(k)
    elseif k.__type == "Closure" then
        return "nil"
    end
    return lit.constant(k)
end

local function aux(op)
    return op and op.AuxValue and op.AuxValue.Value or 0
end

local function methodkey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "unknownMethod"
end

local function tablekey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "?"
end

local function realpcs(proto)
    local slots = ins.auxSlots(proto)
    local pcs = {}
    for pc = 1, #proto.Instructions do
        if not slots[pc] then pcs[#pcs + 1] = pc end
    end
    return pcs, slots
end

local function argsexpr(first, count, openlast)
    if openlast then
        return "__unpack(" .. tostring(first) .. ", __top - 1)"
    end
    local args = {}
    for i = 0, count - 1 do args[#args + 1] = "__get(" .. tostring(first + i) .. ")" end
    return table.concat(args, ", ")
end

local function emitcallresult(out, depth, ra, rc, callexpr)
    if rc == 1 then
        line(out, depth, callexpr)
        line(out, depth, "__top = nil")
        return
    end

    line(out, depth, "local __ret = table.pack(" .. callexpr .. ")")
    if rc == 0 then
        line(out, depth, "for __i = 1, __ret.n do __set(" .. tostring(ra) .. " + __i - 1, __ret[__i]) end")
        line(out, depth, "__top = " .. tostring(ra) .. " + __ret.n")
    else
        local n = rc - 1
        for i = 0, n - 1 do line(out, depth, "__set(" .. tostring(ra + i) .. ", __ret[" .. tostring(i + 1) .. "])") end
        line(out, depth, "__top = nil")
    end
end

local function captureinfo(proto, startpc, child, slots)
    local list = {}
    local pc = startpc
    for i = 1, (child and child.UpvalueCount or 0) do
        while slots[pc] do pc += 1 end
        local op = proto.Instructions[pc]
        if not op or ins.name(op) ~= "CAPTURE" then

            list[i] = { kind = 0, src = nil, malformed = true }
        else
            list[i] = { kind = op.A or 0, src = op.B or 0, pc = pc }
            pc = ins.next(proto, pc, slots)
        end
    end
    return list, pc
end

local function emitcapturearray(out, depth, captures, selfreg)
    local selfvals = {}
    line(out, depth, "local __caps = {}")
    line(out, depth, "local __modes = {}")
    line(out, depth, "local __selfcaps = {}")
    for i, c in ipairs(captures) do
        if c.malformed then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 0 and c.src == selfreg then

            selfvals[#selfvals + 1] = i
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
            line(out, depth, "__selfcaps[" .. tostring(i) .. "] = true")
        elseif c.kind == 0 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = __get(" .. tostring(c.src) .. "), ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 1 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = __cell(" .. tostring(c.src) .. ")")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 1")
        else
            local ui = tostring((c.src or 0) + 1)
            line(out, depth, "local __u" .. tostring(i) .. " = __up[" .. ui .. "]")
            line(out, depth, "if __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".ref then __caps[" .. tostring(i) .. "] = __u" .. tostring(i) .. " else __caps[" .. tostring(i) .. "] = {v = __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".v or nil, ref = false} end")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 2")
        end
    end
    return selfvals
end

local function protomap(parsed)
    local byobject = {}
    for i, p in ipairs(parsed.Protos or {}) do byobject[p] = i end
    return byobject
end

local function closurechild(parsed, proto, op, byobject)
    local name = ins.name(op)
    if name == "NEWCLOSURE" then
        local child = proto.Protos and proto.Protos[(op.D or 0) + 1]
        return child, child and byobject[child] or nil
    elseif name == "DUPCLOSURE" then
        local k = key2(proto, op.D)
        if k and k.__type == "Closure" then
            local id = (k.Value or 0) + 1
            return parsed.Protos and parsed.Protos[id], id
        end
    end
end

local function emitprotofactory(out, parsed, proto, id, byobject, pulse)
    local pcs, slots = realpcs(proto)
    local maxstack = math.max(1, tonumber(proto.MaxStackSize) or 255)
    local params = math.max(0, tonumber(proto.ParameterCount) or 0)
    local pnames = {}
    for i = 0, params - 1 do pnames[#pnames + 1] = "__a" .. tostring(i) end
    if proto.IsVararg then pnames[#pnames + 1] = "..." end

    line(out, 0, "__factory[" .. tostring(id) .. "] = function(__up)")
    line(out, 1, "local function __fn(" .. table.concat(pnames, ", ") .. ")")
    line(out, 2, "local __r, __open = {}, {}")
    line(out, 2, "local __top = nil")
    if proto.IsVararg then line(out, 2, "local __var = table.pack(...)") else line(out, 2, "local __var = {n = 0}") end
    for i = 0, params - 1 do line(out, 2, "__r[" .. tostring(i) .. "] = __a" .. tostring(i)) end

    line(out, 2, "local function __get(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then return __c.v end")
    line(out, 3, "return __r[__i]")
    line(out, 2, "end")
    line(out, 2, "local function __set(__i, __v)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then __c.v = __v else __r[__i] = __v end")
    line(out, 2, "end")
    line(out, 2, "local function __cell(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c == nil then __c = {v = __r[__i], ref = true}; __open[__i] = __c end")
    line(out, 3, "return __c")
    line(out, 2, "end")
    line(out, 2, "local function __close(__a)")
    line(out, 3, "for __i = __a, " .. tostring(maxstack - 1) .. " do")
    line(out, 4, "local __c = __open[__i]")
    line(out, 4, "if __c ~= nil then __r[__i] = __c.v; __open[__i] = nil end")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 2, "local function __unpack(__first, __last)")
    line(out, 3, "if __last == nil or __last < __first then return end")
    line(out, 3, "local __n = __last - __first + 1")
    line(out, 3, "local __a = {n = __n}")
    line(out, 3, "for __i = 1, __n do __a[__i] = __get(__first + __i - 1) end")
    line(out, 3, "return table.unpack(__a, 1, __n)")
    line(out, 2, "end")

    local firstpc = pcs[1] or 1
    line(out, 2, "local __pc = " .. tostring(firstpc))
    line(out, 2, "while true do")

    local consumedcaptures = {}
    for _, pc in ipairs(pcs) do
        if pulse then pulse() end
        local op = proto.Instructions[pc]
        local name = ins.name(op)
        if name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = closurechild(parsed, proto, op, byobject)
            if child then
                local captures = captureinfo(proto, ins.next(proto, pc, slots), child, slots)
                for _, c in ipairs(captures) do if c.pc then consumedcaptures[c.pc] = true end end
            end
        end
    end

    local branchindex = 0
    for _, pc in ipairs(pcs) do
        if pulse then pulse() end
        if not consumedcaptures[pc] then
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local nextpc = ins.next(proto, pc, slots)
            branchindex += 1
            line(out, 3, (branchindex == 1 and "if " or "elseif ") .. "__pc == " .. tostring(pc) .. " then")
            local d = 4
            local ra, rb2, rc, rd = op.A or 0, op.B or 0, op.C or 0, op.D or 0
            local av = aux(op)

            if name == "NOP" or name == "BREAK" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name:match("^FASTCALL") then
                line(out, d, "__pc = " .. tostring(nextpc))
            elseif name == "LOADNIL" then
                line(out, d, "__set(" .. ra .. ", nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADB" then
                line(out, d, "__set(" .. ra .. ", " .. (rb2 == 1 and "true" or "false") .. ")")
                line(out, d, "__pc = " .. tostring(rc ~= 0 and (pc + rc + 1) or nextpc))
            elseif name == "LOADN" then
                line(out, d, "__set(" .. ra .. ", " .. lit.number(rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADKX" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, av) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MOVE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                local value = key == "type" and "__v4type" or (key == "typeof" and "__v4typeof" or (key == "class" and "__classlib" or ("__env[" .. q(key) .. "]")))
                line(out, d, "__set(" .. ra .. ", " .. value .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                line(out, d, "__env[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "__set(" .. ra .. ", __u and __u.v or nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "if __u == nil then __u = {v = nil, ref = true}; __up[" .. tostring(rb2 + 1) .. "] = __u end")
                line(out, d, "__u.v = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "CLOSEUPVALS" then
                line(out, d, "__close(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETIMPORT" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[__get(" .. rc .. ")])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLE" then
                line(out, d, "__get(" .. rb2 .. ")[__get(" .. rc .. ")] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
                local key = tablekey(proto, op, name == "GETUDATAKS")
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. q(key) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
                local key = tablekey(proto, op, name == "SETUDATAKS")
                line(out, d, "__get(" .. rb2 .. ")[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEN" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEN" then
                line(out, d, "__get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWTABLE" then
                line(out, d, "__set(" .. ra .. ", {})"); line(out, d, "__pc = " .. nextpc)
            elseif name == "DUPTABLE" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
                local child, childid = closurechild(parsed, proto, op, byobject)
                local captures, after = captureinfo(proto, nextpc, child, slots)
                local selfvals = emitcapturearray(out, d, captures, ra)
                if childid then
                    if name == "DUPCLOSURE" then
                        line(out, d, "local __cl = __dup(" .. q(tostring(id) .. ":" .. tostring(rd)) .. ", " .. tostring(childid) .. ", __caps, __modes, __selfcaps)")
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    else
                        line(out, d, "local __cl = __factory[" .. tostring(childid) .. "](__caps)")
                        for _, ci in ipairs(selfvals) do line(out, d, "__caps[" .. tostring(ci) .. "].v = __cl") end
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    end
                else
                    line(out, d, "__set(" .. ra .. ", function(...) return nil end)")
                end
                line(out, d, "__pc = " .. tostring(after))
            elseif name == "CAPTURE" then

                line(out, d, "__pc = " .. nextpc)
            elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
                local key = methodkey(proto, op, name == "NAMECALLUDATA")
                local callpc = nextpc
                local callop = proto.Instructions[callpc]
                local callname = callop and ins.name(callop) or ""
                if callop and (callname == "CALL" or callname == "CALLFB") and (callop.A or -1) == ra then
                    local cb, cc = callop.B or 0, callop.C or 0
                    local argtext
                    if cb == 0 then argtext = argsexpr(ra + 2, 0, true) else argtext = argsexpr(ra + 2, math.max(0, cb - 2), false) end
                    local callexpr
                    if lit.identifier(key) then
                        callexpr = "(__get(" .. rb2 .. ")):" .. key .. "(" .. argtext .. ")"
                    else
                        local pre = "(__get(" .. rb2 .. "))[" .. q(key) .. "]"
                        if argtext ~= "" then argtext = "__get(" .. rb2 .. "), " .. argtext else argtext = "__get(" .. rb2 .. ")" end
                        callexpr = "(" .. pre .. ")(" .. argtext .. ")"
                    end
                    emitcallresult(out, d, ra, cc, callexpr)
                    line(out, d, "__pc = " .. tostring(ins.next(proto, callpc, slots)))
                else
                    line(out, d, "local __obj = __get(" .. rb2 .. ")")
                    line(out, d, "__set(" .. ra .. ", __obj[" .. q(key) .. "])")
                    line(out, d, "__set(" .. tostring(ra + 1) .. ", __obj)")
                    line(out, d, "__pc = " .. nextpc)
                end
            elseif name == "CALL" or name == "CALLFB" then
                local argtext
                if rb2 == 0 then argtext = argsexpr(ra + 1, 0, true) else argtext = argsexpr(ra + 1, math.max(0, rb2 - 1), false) end
                emitcallresult(out, d, ra, rc, "(__get(" .. ra .. "))(" .. argtext .. ")")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "RETURN" then
                if rb2 == 1 then line(out, d, "return")
                elseif rb2 == 0 then line(out, d, "return __unpack(" .. ra .. ", (__top or " .. ra .. ") - 1)")
                else
                    local vals = {}
                    for r = ra, ra + rb2 - 2 do vals[#vals + 1] = "__get(" .. tostring(r) .. ")" end
                    line(out, d, "return " .. table.concat(vals, ", "))
                end
            elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "JUMPIF" or name == "JUMPIFNOT" then
                local test = name == "JUMPIF" and ("__get(" .. ra .. ")") or ("not __get(" .. ra .. ")")
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
                local rb = bit32.band(av, 0xff)
                local cmp = ({JUMPIFEQ = "==", JUMPIFNOTEQ = "~=", JUMPIFLT = "<", JUMPIFLE = "<=", JUMPIFNOTLT = "<", JUMPIFNOTLE = "<="})[name]
                local test = "__get(" .. ra .. ") " .. cmp .. " __get(" .. rb .. ")"
                if name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" then
                local rhs
                if name == "JUMPXEQKNIL" then rhs = "nil"
                elseif name == "JUMPXEQKB" then rhs = bit32.band(av, 1) == 1 and "true" or "false"
                else rhs = constexpr(proto, bit32.band(av, 0xffffff)) end
                local test = "__get(" .. ra .. ") == " .. rhs
                if bit32.btest(av, 0x80000000) then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
                local symbol = ({ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " __get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" then
                local symbol = ({ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " " .. constexpr(proto, rc) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SUBRK" or name == "DIVRK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rb2) .. (name == "SUBRK" and " - " or " / ") .. "__get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "AND" or name == "OR" then
                if name == "AND" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rc .. ")) else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", __get(" .. rc .. ")) end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "ANDK" or name == "ORK" then
                local kval = constexpr(proto, rc)
                if name == "ANDK" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", " .. kval .. ") else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", " .. kval .. ") end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CONCAT" then
                line(out, d, "local __x = __get(" .. rc .. ")")
                for r = rc - 1, rb2, -1 do line(out, d, "__x = __get(" .. r .. ") .. __x") end
                line(out, d, "__set(" .. ra .. ", __x)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NOT" then
                line(out, d, "__set(" .. ra .. ", not __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MINUS" then
                line(out, d, "__set(" .. ra .. ", -__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LENGTH" then
                line(out, d, "__set(" .. ra .. ", #__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETLIST" then
                line(out, d, "local __t = __get(" .. ra .. ")")
                if rc == 0 then
                    line(out, d, "local __n = (__top or " .. rb2 .. ") - " .. rb2)
                    line(out, d, "for __i = 0, __n - 1 do __t[" .. av .. " + __i] = __get(" .. rb2 .. " + __i) end")
                    line(out, d, "__top = nil")
                else
                    for i = 0, rc - 2 do line(out, d, "__t[" .. tostring(av + i) .. "] = __get(" .. tostring(rb2 + i) .. ")") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "FORNPREP" then
                line(out, d, "local __limit = __fornum(__get(" .. ra .. "))")
                line(out, d, "local __step = __fornum(__get(" .. tostring(ra + 1) .. "))")
                line(out, d, "local __idx = __fornum(__get(" .. tostring(ra + 2) .. "))")
                line(out, d, "__set(" .. ra .. ", __limit); __set(" .. tostring(ra + 1) .. ", __step); __set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. nextpc .. " else __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " end")
            elseif name == "FORNLOOP" then
                line(out, d, "local __limit, __step = __get(" .. ra .. "), __get(" .. tostring(ra + 1) .. ")")
                line(out, d, "local __idx = __get(" .. tostring(ra + 2) .. ") + __step")
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then

                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGPREP" then
                line(out, d, "local __g = __get(" .. ra .. ")")
                line(out, d, "if type(__g) ~= \"function\" then")
                line(out, d + 1, "local __ng, __ns, __ni = __iterprep(__g)")
                line(out, d + 1, "__set(" .. ra .. ", __ng); __set(" .. tostring(ra + 1) .. ", __ns); __set(" .. tostring(ra + 2) .. ", __ni)")
                line(out, d, "end")
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGLOOP" then
                local count = math.max(1, bit32.band(av, 0xff))
                line(out, d, "local __ret = table.pack((__get(" .. ra .. "))(__get(" .. tostring(ra + 1) .. "), __get(" .. tostring(ra + 2) .. ")))")
                for i = 1, count do line(out, d, "__set(" .. tostring(ra + 2 + i) .. ", __ret[" .. tostring(i) .. "])") end
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __ret[1])")
                line(out, d, "if __ret[1] ~= nil then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "GETVARARGS" then
                if rb2 == 0 then
                    line(out, d, "for __i = 1, __var.n do __set(" .. ra .. " + __i - 1, __var[__i]) end")
                    line(out, d, "__top = " .. ra .. " + __var.n")
                else
                    for i = 1, rb2 - 1 do line(out, d, "__set(" .. tostring(ra + i - 1) .. ", __var[" .. tostring(i) .. "])") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CMPPROTO" then


                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "NEWCLASS" then
                line(out, d, "local __super = " .. (rb2 ~= 0xff and ("__get(" .. rb2 .. ")") or "nil"))
                line(out, d, "__set(" .. ra .. ", __newclass(" .. constexpr(proto, av) .. ", __super))")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLASSMEMBER" then
                local key = rawstr(key2(proto, av)) or "member"
                line(out, d, "__classmember(__get(" .. ra .. "), " .. q(key) .. ", __get(" .. rc .. "))")
                line(out, d, "__pc = " .. nextpc)
            else

                line(out, d, "error(" .. q("LumenV4 VM fallback: unknown opcode " .. tostring(name) .. " at pc " .. tostring(pc)) .. ")")
            end
        end
    end

    line(out, 3, "else")
    line(out, 4, "error(\"LumenV4 VM fallback: invalid pc \" .. tostring(__pc))")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 1, "end")
    line(out, 1, "return __fn")
    line(out, 0, "end")
    line(out, 0, "")
end

function vm.run(parsed, reason)
    local entry = assert(parsed and parsed.Protos and parsed.Protos[parsed.ProtoEntryPoint], "LumenV4 VM fallback: missing entry proto")
    local slice = os.clock()
    local function pulse(force)
        local now = os.clock()
        if force or now - slice >= 0.008 then
            if task and type(task.wait) == "function" then task.wait() end
            slice = os.clock()
        end
    end
    local byobject = protomap(parsed)
    local decoded = 0
    for _, proto in ipairs(parsed.Protos or {}) do
        pulse()
        local pcs = realpcs(proto)
        decoded += #pcs
    end
    local bytecodeversion = tonumber(parsed.BytecodeVersion) or 0
    local header = ("-- LumenV4 status=VM_FALLBACK coverage=100.00 reachable=%d covered=%d blocks=%d structuredBlocks=0 fallbackBlocks=%d phis=0 undefs=0 packs=0 cells=0 objects=0 escapedObjects=0 irreducible=0 bytecodeVersion=%d ssa=false parser=true diagnostics=0")
        :format(decoded, decoded, decoded, decoded, bytecodeversion)
    local out = {
        header,
        "-- Structured recovery failed; this function is a direct decoded-bytecode state machine.",
        "-- Original recovery reason: " .. tostring(reason or "semantic fallback"):gsub("[\r\n]+", " "),
        "local __env = (getfenv and getfenv(0)) or _G",
        "local __factory = {}",
        "local __dupcache = {}",
        "",
        "local function __fornum(v)",
        "    if type(v) == \"number\" then return v end",
        "    local n = tonumber(v)",
        "    if n == nil then error(\"invalid 'for' limit/step/index (number expected)\", 2) end",
        "    return n",
        "end",
        "",
        "local function __mt(v)",
        "    if type(getrawmetatable) == \"function\" then",
        "        local ok, mt = pcall(getrawmetatable, v)",
        "        if ok and mt ~= nil then return mt end",
        "    end",
        "    return getmetatable(v)",
        "end",
        "",
        "local function __iterprep(v)",
        "    if type(v) == \"table\" then",
        "        local mt = __mt(v)",
        "        local it = mt and mt.__iter",
        "        if it ~= nil then",
        "            local g, s, i = it(v)",
        "            return g, s, i",
        "        end",
        "        if mt and mt.__call then return v, nil, nil end",
        "        return next, v, nil",
        "    end",
        "    local mt = __mt(v)",
        "    local it = mt and mt.__iter",
        "    if it ~= nil then return it(v) end",
        "    return v, nil, nil",
        "end",
        "",
        "local __realtype = type",
        "local __realtypeof = typeof or type",
        "local __classof = setmetatable({}, {__mode = \"k\"})",
        "local __classmeta = setmetatable({}, {__mode = \"k\"})",
        "local __isclass = setmetatable({}, {__mode = \"k\"})",
        "",
        "local function __classshape(name, props, methods)",
        "    return {__name = name, __props = props, __methods = methods}",
        "end",
        "",
        "local function __classlookup(cls, key)",
        "    local c = cls",
        "    while c do",
        "        local v = rawget(c, key)",
        "        if v ~= nil then return v end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return nil",
        "end",
        "",
        "local function __isinstance(obj, cls)",
        "    if not __isclass[cls] then return false end",
        "    local c = __classof[obj]",
        "    while c do",
        "        if c == cls then return true end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return false",
        "end",
        "",
        "local __classlib = setmetatable({",
        "    isinstance = __isinstance,",
        "    classof = function(v) return __classof[v] end,",
        "}, {__index = __env.class})",
        "",
        "local function __v4type(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtype(v)",
        "end",
        "local function __v4typeof(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtypeof(v)",
        "end",
        "",
        "local __classmetamethods = {",
        "    __add=true,__sub=true,__mul=true,__div=true,__idiv=true,__mod=true,__pow=true,",
        "    __unm=true,__len=true,__eq=true,__lt=true,__le=true,__concat=true,__tostring=true,",
        "    __iter=true,__call=true,",
        "}",
        "",
        "local function __classmember(cls, name, value)",
        "    rawset(cls, name, value)",
        "    local m = __classmeta[cls]",
        "    if m and __classmetamethods[name] then",
        "        m.instanceMt[name] = function(...) return value(...) end",
        "    end",
        "end",
        "",
        "local function __newclass(shape, super)",
        "    local cls = {}",
        "    local props, propset = {}, {}",
        "    if super and __classmeta[super] then",
        "        for _, p in ipairs(__classmeta[super].props) do props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    for _, p in ipairs(shape and shape.__props or {}) do",
        "        if not propset[p] then props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    local imt = {}",
        "    local meta = {shape = shape or {}, super = super, props = props, propset = propset, instanceMt = imt}",
        "    __classmeta[cls] = meta",
        "    __isclass[cls] = true",
        "    imt.__index = function(obj, key)",
        "        local v = __classlookup(cls, key)",
        "        if v ~= nil then return v end",
        "        if propset[key] then return nil end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    imt.__newindex = function(obj, key, value)",
        "        if propset[key] then rawset(obj, key, value); return end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    local cmt = {}",
        "    cmt.__index = function(_, key)",
        "        local v = super and __classlookup(super, key) or nil",
        "        if v ~= nil then return v end",
        "        error(\"this class does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    cmt.__newindex = function(_, key) error(\"attempt to index class with '\" .. tostring(key) .. \"'\", 2) end",
        "    cmt.__call = function(_, init)",
        "        local obj = {}",
        "        __classof[obj] = cls",
        "        setmetatable(obj, imt)",
        "        if init ~= nil then",
        "            for _, p in ipairs(props) do rawset(obj, p, init[p]) end",
        "        end",
        "        return obj",
        "    end",
        "    setmetatable(cls, cmt)",
        "    return cls",
        "end",
        "",
        "local function __samecaps(a, b, modes, selfcaps, fn)",
        "    if not a then return false end",
        "    for i = 1, #b do",
        "        if modes[i] == 0 then",
        "            local expected = selfcaps[i] and fn or (b[i] and b[i].v)",
        "            if not rawequal(a[i] and a[i].v, expected) then return false end",
        "        elseif modes[i] == 2 then",
        "            local ar, br = a[i] and a[i].ref, b[i] and b[i].ref",
        "            if ar or br then",
        "                if a[i] ~= b[i] then return false end",
        "            elseif not rawequal(a[i] and a[i].v, b[i] and b[i].v) then return false end",
        "        elseif a[i] ~= b[i] then return false end",
        "    end",
        "    return true",
        "end",
        "",
        "local function __dup(cacheKey, id, caps, modes, selfcaps)",
        "    local c = __dupcache[cacheKey]",
        "    if c ~= nil and __samecaps(c.caps, caps, modes, selfcaps, c.fn) then return c.fn end",
        "    local fn = __factory[id](caps)",
        "    for i in pairs(selfcaps) do caps[i].v = fn end",
        "    if c == nil then __dupcache[cacheKey] = {fn = fn, caps = caps, modes = modes} end",
        "    return fn",
        "end",
        "",
    }

    for i, proto in ipairs(parsed.Protos or {}) do pulse(); emitprotofactory(out, parsed, proto, i, byobject, pulse) end
    pulse(true)
    local entryid = byobject[entry] or parsed.ProtoEntryPoint
    line(out, 0, "return (__factory[" .. tostring(entryid) .. "]({}))()")

    local source = table.concat(out, "\n")
    if type(loadstring) == "function" then
        local fn, err = loadstring(source, "@LumenV4/vm-fallback-verify")
        if not fn then error("LumenV4 VM fallback generator emitted invalid Luau: " .. tostring(err), 2) end
    end
    return source, {
        status = "VM_FALLBACK",
        fallback = true,
        syntaxValid = true,
        originCoverageValid = true,
        coverage = 1,
        verification = "decoded-bytecode-total-dispatch",
        structuredError = tostring(reason or ""),
    }
end

return vm
end)()

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

local function hashard(st)

    return #st.bad > 0
end

function decomp.new(opt) return setmetatable({ opt = opt or {}, deadline = nil, slice = os.clock() }, decomp) end

function decomp:_check()
    local now = os.clock()
    if now - (self.slice or now) >= 0.008 then
        if task and type(task.wait) == "function" then task.wait() end
        self.slice = os.clock()
        now = self.slice
    end
    if self.deadline and now > self.deadline then
        error("LumenV4: STRUCTURED_BUDGET exceeded", 2)
    end
end

function decomp:_state(proto, up, ph)
    self:_check()
    local limits = {
        maxinstructions = self.opt.structuredmaxprotoinstructions or self.opt.structuredmaxinstructions,
        maxblocks = self.opt.structuredmaxblocks,
    }
    local ir = irbuild.run(proto, function() self:_check() end, limits)
    ir.paramhints = ph or {}
    self:_check()
    ir = irpass.run(ir, self.opt, function() self:_check() end)
    self:_check()
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    local st = context.new(proto, ir, naming, up, lower.new(), self.opt)
    st.v4 = { fallback = false, visited = {}, status = "STRUCTURED", cellNames = {} }


    if ir.cells and next(ir.cells) then
        local oldvname = st.vname
        local ids = {}
        for cid in pairs(ir.cells) do ids[#ids + 1] = cid end
        table.sort(ids)
        local resolvedcell = {}
        for raw, cid in pairs(ir.cellOfValue or {}) do
            local rv = ir:resolve(raw)
            if rv then resolvedcell[rv] = resolvedcell[rv] or cid end
        end
        for _, cid in ipairs(ids) do
            local cell = ir.cells[cid]
            local cp = cell.captures and cell.captures[1]
            local raw = cp and ir.ssa.usesByPC[cp] and ir.ssa.usesByPC[cp][cell.reg] or nil
            if raw then
                st.v4.cellNames[cid] = oldvname(st, raw, cell.reg, nil, cp)
            else
                st.v4.cellNames[cid] = naming:unique("cell" .. tostring(cid))
            end
        end
        st.vname = function(self, value, reg, hint, pc)
            local cid = value and ((self.ir.cellOfValue and self.ir.cellOfValue[value]) or resolvedcell[self.ir:resolve(value)])
            local cellname = cid and self.v4.cellNames[cid]
            if cellname then return cellname end
            return oldvname(self, value, reg, hint, pc)
        end
    end


    for bid, phis in pairs(ir.phis or {}) do
        local block = assert(ir.cfg.blocks[bid], "LumenV4: phi references invalid CFG block")
        for reg, phi in pairs(phis) do
            local pid = ir:resolve(phi.id)
            if pid and not ir.dead[pid] then
                local target = st:vname(pid, reg, nil, block.startPC)
                for pred, raw in pairs(phi.incoming or {}) do
                    local rid = ir:resolve(raw)
                    local value = rid and ir.vals[rid] or nil
                    if value and value.kind ~= "undef" then
                        local pb = assert(ir.cfg.blocks[pred], "LumenV4: phi references invalid predecessor")
                        local source = st:vname(rid, reg, nil, pb.endPC)
                        if source ~= target then
                            error(("LumenV4: UNSUPPORTED SSA destruction mismatch for phi v%d r%d: b%d uses %s, target is %s")
                                :format(pid, reg, pred, tostring(source), tostring(target)), 2)
                        end
                    end
                end
            end
        end
    end
    st.v4.ssaDestructionVerified = true
    return st
end

local function arguments(st, proto)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    return args
end

local function preparepacks(st)
    st.packnames = {}
    st.directPacks = {}
    st.directPackValues = {}

    local consumers = {}
    for pc, producer in pairs(st.ssa.packInput or {}) do
        if type(producer) == "number" then
            local list = consumers[producer]
            if not list then list = {}; consumers[producer] = list end
            list[#list + 1] = pc
        end
    end

    local pcs = {}
    for pc, pack in pairs(st.ssa.packsByPC or {}) do
        if pack and pack.producesTop then pcs[#pcs + 1] = pc end
    end
    table.sort(pcs)

    local names = {}
    for _, pc in ipairs(pcs) do
        local list = consumers[pc] or {}
        local consumer = #list == 1 and list[1] or nil
        local sameblock = consumer and st.cfg.blockmap[pc] == st.cfg.blockmap[consumer]
        if consumer and sameblock and st:next(pc) == consumer then


            st.directPacks[pc] = consumer
        else
            local name = st.naming:unique("__pack" .. tostring(pc))
            st.packnames[pc] = name
            st.declared[name] = 0
            names[#names + 1] = name
        end
    end

    for i = 1, #names, 8 do
        local chunk = {}
        for j = i, math.min(i + 7, #names) do chunk[#chunk + 1] = names[j] end
        st:out("local " .. table.concat(chunk, ", "))
    end
end

local function packtail(st, pc)
    local producer = st.ssa.packInput and st.ssa.packInput[pc] or nil
    if producer == st.ssa.ambiguousPack then
        error("LumenV4: UNSUPPORTED divergent ValuePack at pc " .. tostring(pc), 2)
    end
    if type(producer) ~= "number" then
        error("LumenV4: UNSUPPORTED open ValuePack consumer without unique producer at pc " .. tostring(pc), 2)
    end
    local _, _, pp = regs.readWrite(st.proto.Instructions[producer])
    local direct = st.directPackValues and st.directPackValues[producer]
    if direct then return producer, pp.openWriteFrom, direct.node end
    local name = assert(st.packnames and st.packnames[producer], "LumenV4: missing ValuePack temp")
    return producer, pp.openWriteFrom, ex.atom("table.unpack(" .. name .. ", 1, " .. name .. ".n)", false)
end

function decomp:_op(st, pc)
    local op = st.proto.Instructions[pc]
    local _, _, pack = regs.readWrite(op)
    st.top = nil
    if pack.consumesTop then
        local _, base, node = packtail(st, pc)
        if type(base) ~= "number" then error("LumenV4: invalid ValuePack producer at pc " .. tostring(pc), 2) end
        if pack.openReadFrom and base < pack.openReadFrom then
            error("LumenV4: invalid ValuePack base at pc " .. tostring(pc), 2)
        end
        st.top = { reg = base, node = node, v4 = true }
    end

    local name = ins.name(op)
    local nx

    if name == "NEWTABLE" then
        st:set(pc, op.A, ex.atom("{}", false))
        nx = st:next(pc)
    elseif name == "DUPTABLE" then
        local constant = st.proto.Constants and st.proto.Constants[(op.D or 0) + 1]
        st:set(pc, op.A, ex.atom(lit.constant(constant), false))
        nx = st:next(pc)
    else
        nx = ops.run(self, st, pc)
    end

    if pack.producesTop then
        local produced = st.top
        if not produced or not produced.node then
            error("LumenV4: open-result producer did not expose a ValuePack at pc " .. tostring(pc), 2)
        end
        local base = assert(pack.openWriteFrom, "LumenV4: ValuePack producer has no base")
        if st.directPacks and st.directPacks[pc] then
            st.directPackValues[pc] = { reg = base, node = produced.node }
        else
            local name = assert(st.packnames and st.packnames[pc], "LumenV4: missing producer ValuePack temp")
            st:out(name .. " = table.pack(" .. ex.str(produced.node) .. ")")
            for reg, version in pairs(st.ssa.defsByPC[pc] or {}) do
                if reg >= base then
                    local node = ex.atom(name .. "[" .. tostring(reg - base + 1) .. "]", false)
                    st.vals[version] = node
                    st.expr[version] = node
                end
            end
        end
        st.top = nil
    end
    return nx
end

function decomp:_child(proto, up, ph)
    self:_check()
    local st = self:_state(proto, up, ph)
    local args = arguments(st, proto)
    preparepacks(st)
    self:_region(st, 1, #proto.Instructions + 1, {})

    if hashard(st) then

        st = self:_state(proto, up, ph)
        args = arguments(st, proto)
        preparepacks(st)
        st.v4.fallback = true
        st.v4.status = "LOSSLESS_FALLBACK"
        self:_dispatcher(st)
        if hashard(st) then
            error("LumenV4: UNSUPPORTED semantic lowering issue: " .. table.concat(st.bad, " | "), 2)
        end
    end

    self:_check()
    local root = astpass.run(st.ast:done(), self.opt)
    self:_check()
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, a = info.loop, op.A


    local body = st:next(pc)
    local varreg = a + 2
    local bodystart = body
    local first = st.proto.Instructions[body]
    if first and ins.name(first) == "MOVE" and first.B == a + 2 and first.A == a + 3 then
        varreg = a + 3
        st.v4.visited[body] = true
        bodystart = st:next(body)
    end

    local old = st.alias[varreg]
    local lv = varreg == a + 2 and st:veruse(body, varreg) or st:verdef(body, varreg)
    if not lv then lv = st:veruse(loop, a + 2) or st:verdef(loop, a + 2) end
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, varreg, bodystart, loop) and "_" or st:vname(lv, varreg, fall, body)
    local limit, step, init = ex.str(st:loopx(pc, loop, a)), ex.str(st:loopx(pc, loop, a + 1)), ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head ..= ", " .. step end
    st:out(head .. " do"); st.indent += 1
    st.alias[varreg] = var; st.declared[var] = st.indent
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, bodystart, loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end"); st.alias[varreg] = old
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, lop = info.loop, info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth, vars, old = (active.loopdepth or 0) + 1, {}, {}
    for i = 1, n do
        local r = op.A + 2 + i; old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end
    local src
    local rs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A); local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, rs) then src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2)) end
    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do"); st.indent += 1
    for i = 1, n do local r = op.A + 2 + i; st.alias[r] = vars[i]; st.declared[vars[i]] = st.indent end
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then"); st.indent += 1
    local old = active.join; active.join = info.join
    self:_region(st, info.a, info.b, active); active.join = old
    st:trim(st.indent); st.indent -= 1
    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then self:_emitif(st, sub, active, "elseif"); return end
        st:out("else"); st.indent += 1; old = active.join; active.join = info.join
        self:_region(st, info.c, info.d, active); active.join = old
        st:trim(st.indent); st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start; active = active or {}
    local budgettick = 0
    while pc < stop and pc <= #st.proto.Instructions do
        budgettick += 1
        if budgettick >= 64 then budgettick = 0; self:_check() end
        if st.cfg.aux[pc] then pc += 1
        elseif st.consumed[pc] then st.v4.visited[pc] = true; pc += 1
        else
            st.v4.visited[pc] = true
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then


                st:hoist(pc)
                active["repeat:" .. tostring(pc)] = true; st:out("repeat"); st.indent += 1
                local prev = active.loop; active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active); active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch]); st.v4.visited[rep.latch] = true
                st:trim(st.indent); st.indent -= 1; st:out("until " .. ex.str(x)); active["repeat:" .. tostring(pc)] = nil; pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then

                    st:hoist(pc)
                    st:out("while true do"); st.indent += 1; local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active); active.loop = prev; st.v4.visited[forever.latch] = true
                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]; local name = ins.name(op)
                    if name == "FORNPREP" then pc = self:_numfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then pc = self:_genfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "CMPPROTO" then
                        local target, join = ins.jumpTarget(pc, op), st:join(pc)
                        if join and target > pc and target < join and join <= stop then self:_region(st, target, join, active); pc = join
                        else st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target)); pc = st:next(pc) end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop, target = active.loop, ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end"); pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc); st:out("while " .. ex.str(wh.cond) .. " do"); st.indent += 1
                                    local prev = active.loop; active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active); active.loop = prev
                                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then st:hoist(info.join); self:_emitif(st, info, active); pc = info.join
                                    else st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target)); pc = st:next(pc) end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target, loop = ins.jumpTarget(pc, op), active.loop
                        if loop and target == loop.breakpc then st:out("break"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("continue"); pc = st:next(pc)
                        elseif target == stop or target == active.join then pc = stop
                        else st:badpc(pc, "unstructured jump -> " .. tostring(target)); pc = st:next(pc) end
                    else pc = self:_op(st, pc) end
                end
            end
        end
    end
    return pc
end

local function dispatcherunsupported(st)
    for _, n in ipairs(st.ir.ops) do
        local name = n.name
        if name == "FORNPREP" or name == "FORNLOOP" or name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" or name == "FORGLOOP" then
            return "dispatcher requires VM loop-state emulation for " .. name .. " at pc " .. tostring(n.pc)
        end
        if name == "CMPPROTO" then return "CMPPROTO cannot be represented losslessly in source fallback at pc " .. tostring(n.pc) end
        if name == "CLOSEUPVALS" then return "dispatcher would change upvalue close/cell lifetime at pc " .. tostring(n.pc) end
        if name == "CAPTURE" and n.op.A == 1 then return "dispatcher would hoist a by-reference captured local cell at pc " .. tostring(n.pc) end
    end
end

function decomp:_dispatcher(st)
    local why = dispatcherunsupported(st)
    if why then error("LumenV4: UNSUPPORTED lossless fallback: " .. why, 2) end


    local nameset, ordered = {}, {}
    for id, v in ipairs(st.ir.vals) do
        if v and not st.ir.dead[id] and v.kind ~= "param" and v.kind ~= "undef" then
            local name = st:vname(id, v.reg, nil, v.pc or 1)
            if name and not nameset[name] and st.declared[name] == nil then nameset[name] = true; ordered[#ordered + 1] = name end
        end
    end
    table.sort(ordered)
    for i = 1, #ordered, 12 do
        local chunk = {}; for j = i, math.min(i + 11, #ordered) do chunk[#chunk + 1] = ordered[j]; st.declared[ordered[j]] = 0 end
        st:out("local " .. table.concat(chunk, ", "))
    end

    local state = st.naming:unique("__lumenstate")
    st.declared[state] = 0
    st:out("local " .. state .. " = 1")
    st:out("while true do"); st.indent += 1

    for bi, b in ipairs(st.cfg.blocks) do
        st:out((bi == 1 and "if " or "elseif ") .. state .. " == " .. tostring(b.id) .. " then")
        st.indent += 1
        st.top = nil
        for pi, pc in ipairs(b.pcs) do
            st.v4.visited[pc] = true
            if not st.consumed[pc] then
                local op, name = st.proto.Instructions[pc], ins.name(st.proto.Instructions[pc])
                local last = pi == #b.pcs
                if last and ins.isConditional(op) then
                    local target, fall = st.cfg.blockmap[ins.jumpTarget(pc, op)], st.cfg.blockmap[st:next(pc)]
                    if not target or not fall then error("LumenV4: invalid dispatcher conditional edge at pc " .. tostring(pc), 2) end
                    st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then")
                    st.indent += 1; st:out(state .. " = " .. tostring(target)); st.indent -= 1
                    st:out("else"); st.indent += 1; st:out(state .. " = " .. tostring(fall)); st.indent -= 1; st:out("end")
                elseif last and (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") then
                    local target = st.cfg.blockmap[ins.jumpTarget(pc, op)]
                    if not target then error("LumenV4: invalid dispatcher jump edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                elseif last and name == "LOADB" and (op.C or 0) ~= 0 then
                    self:_op(st, pc)
                    local target = st.cfg.blockmap[pc + op.C + 1]
                    if not target then error("LumenV4: invalid LOADB edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                else
                    self:_op(st, pc)
                    if last and name ~= "RETURN" then
                        if #b.successors == 1 then st:out(state .. " = " .. tostring(b.successors[1]))
                        elseif #b.successors == 0 then st:out("break")
                        elseif #b.successors > 1 then error("LumenV4: unhandled multi-successor block at pc " .. tostring(pc), 2) end
                    end
                end
            end
        end
        st.indent -= 1
    end
    st:out("else"); st.indent += 1; st:out("error(\"LumenV4: invalid dispatcher state \" .. tostring(" .. state .. "))"); st.indent -= 1
    st:out("end")
    st.indent -= 1; st:out("end")
end

local function metrics(st)
    local reachable, covered = 0, 0
    for pc = 1, #st.proto.Instructions do
        if not st.cfg.aux[pc] and st.cfg.blockmap[pc] then
            reachable += 1
            if st.v4.visited[pc] or st.consumed[pc] then covered += 1 end
        end
    end
    return reachable, covered, reachable == 0 and 1 or covered / reachable
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    local src = printer.run(root, self.opt)
    local reachable, covered, coverage = metrics(st)
    if covered ~= reachable then
        error(("LumenV4: PARTIAL origin coverage %d/%d (%.2f%%)"):format(covered, reachable, coverage * 100), 2)
    end
    local ss = st.ssa:summary()
    local structuredblocks = st.v4.fallback and 0 or #st.cfg.blocks
    local fallbackblocks = st.v4.fallback and #st.cfg.blocks or 0
    local objectcount, escapedobjects = 0, 0
    for _, obj in pairs(st.ir.objects or {}) do
        objectcount += 1
        if obj.escaped then escapedobjects += 1 end
    end
    local cellcount = 0
    for _ in pairs(st.ir.cells or {}) do cellcount += 1 end
    local packcount = 0
    for _, pack in pairs(st.ssa.packsByPC or {}) do if pack and pack.producesTop then packcount += 1 end end
    local irreducible = st.cfg.irreducible and 1 or 0
    local bytecodeversion = self.parsed and self.parsed.BytecodeVersion or 0

    if type(loadstring) ~= "function" then
        error("LumenV4: UNSUPPORTED syntax verification requires loadstring()", 2)
    end

    local header = ("-- LumenV4 status=%s coverage=%.2f reachable=%d covered=%d blocks=%d structuredBlocks=%d fallbackBlocks=%d phis=%d undefs=%d packs=%d cells=%d objects=%d escapedObjects=%d irreducible=%d bytecodeVersion=%d ssa=true parser=true diagnostics=%d\n")
        :format(st.v4.status, coverage * 100, reachable, covered, #st.cfg.blocks, structuredblocks, fallbackblocks,
            ss.phis or 0, ss.undefs or 0, packcount, cellcount, objectcount, escapedobjects, irreducible, bytecodeversion, #st.bad)
    src = header .. src
    local check, err = loadstring(src, "@LumenV4/verify")
    if not check then error("LumenV4: INVALID emitted Luau: " .. tostring(err), 2) end

    return src, {
        status = st.v4.status, cfg = st.cfg, ir = st.ir, ssa = st.ssa, ssaSummary = ss, issues = st.bad,
        coverage = coverage, coveredInstructions = covered, reachableInstructions = reachable, fallback = st.v4.fallback,
        syntaxValid = true, originCoverageValid = true, verification = "syntax+CFG-origin-invariants",
        objectCount = objectcount, escapedObjects = escapedobjects, cellCount = cellcount, valuePackCount = packcount,
        irreducible = st.cfg.irreducible == true, bytecodeVersion = bytecodeversion,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenV4: parsed bytecode has no entry proto")
    self.parsed = parsed

    local totalinstructions = 0
    local maxprotoinstructions = 0
    for _, p in ipairs(parsed.Protos or {}) do
        local n = #(p.Instructions or {})
        totalinstructions += n
        if n > maxprotoinstructions then maxprotoinstructions = n end
    end
    local maxtotal = tonumber(self.opt.structuredmaxinstructions) or 8000
    local maxproto = tonumber(self.opt.structuredmaxprotoinstructions) or 4000
    local structurederror
    if (maxtotal > 0 and totalinstructions > maxtotal) or (maxproto > 0 and maxprotoinstructions > maxproto) then
        structurederror = "LumenV4: STRUCTURED_COMPLEXITY total=" .. tostring(totalinstructions) .. " maxproto=" .. tostring(maxprotoinstructions)
    else
        local budget = tonumber(self.opt.structuredbudget) or 1.25
        self.slice = os.clock()
        self.deadline = budget > 0 and (self.slice + budget) or nil
        local ok, src, info = pcall(function() return self:decompileProto(proto, {}) end)
        self.deadline = nil
        if ok then
            self.parsed = nil
            return src, info
        end
        structurederror = tostring(src)
    end

    self.deadline = nil
    self.slice = os.clock()
    local fok, fsrc, finfo = pcall(function()
        return vmfallback.run(parsed, structurederror)
    end)
    self.parsed = nil

    if not fok then
        error("LumenV4: VM fallback generator failure after structured failure: " .. tostring(fsrc)
            .. " | structured: " .. structurederror, 2)
    end
    return fsrc, finfo
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
    ["main.ir.build"] = [===[local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local regs = require("main.analysis.registers")
local ins = require("main.bytecode.instructions")
local fx = require("main.ir.effects")
local fn = require("main.ir.function")
local val = require("main.ir.value")
local block = require("main.ir.block")

local build = {}

local function copyset(src)
    local out = {}; if src then for k in pairs(src) do out[k] = true end end; return out
end
local function unionset(dst, src)
    local changed = false
    if src then for k in pairs(src) do if not dst[k] then dst[k] = true; changed = true end end end
    return changed
end
local function seteq(a, b)
    a, b = a or {}, b or {}
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end


local function copystate(src)
    local out = {}
    for r, set in pairs(src or {}) do out[r] = copyset(set) end
    return out
end

local function stateeq(a, b)
    a, b = a or {}, b or {}
    for r, set in pairs(a) do if not seteq(set, b[r]) then return false end end
    for r, set in pairs(b) do if not seteq(set, a[r]) then return false end end
    return true
end


local function analyzecells(out, check)
    local capturecell, capturereg, nextcell = {}, {}, 1
    for _, n in ipairs(out.ops) do
        if n.name == "CAPTURE" and n.op.A == 1 then
            capturecell[n.pc] = nextcell
            capturereg[nextcell] = n.op.B
            nextcell += 1
        end
    end

    if nextcell == 1 then
        out.cells, out.cellOfValue, out.captureCell = {}, {}, capturecell
        return out
    end

    local instate, outstate = {}, {}
    local function merged(block)
        if block.id == 1 then return {} end
        local result = {}
        for _, pred in ipairs(block.predecessors) do
            for r, set in pairs(outstate[pred] or {}) do
                local dst = result[r]
                if not dst then dst = {}; result[r] = dst end
                unionset(dst, set)
            end
        end
        return result
    end

    local function transfer(block, incoming)
        local state = copystate(incoming)
        for _, pc in ipairs(block.pcs) do
            local op = out.proto.Instructions[pc]
            local name = ins.name(op)
            if name == "CAPTURE" and op.A == 1 then
                local set = state[op.B]
                if not set then set = {}; state[op.B] = set end
                set[capturecell[pc]] = true
            elseif name == "CLOSEUPVALS" then
                for r in pairs(state) do if r >= (op.A or 0) then state[r] = nil end end
            end
        end
        return state
    end

    local changed, iterations = true, 0
    local limit = math.max(32, #out.cfg.blocks * (nextcell + 8) * 4)
    while changed do
        if check then check() end
        iterations += 1
        if iterations > limit then error("LumenV4: CellId dataflow failed to converge", 2) end
        changed = false
        for _, b in ipairs(out.cfg.blocks) do
            local incoming = merged(b)
            if not stateeq(instate[b.id], incoming) then instate[b.id] = incoming; changed = true end
            local outgoing = transfer(b, incoming)
            if not stateeq(outstate[b.id], outgoing) then outstate[b.id] = outgoing; changed = true end
        end
    end

    local valuecells, closesites = {}, {}
    local function markvalue(version, set)
        if not version or not set or not next(set) then return end
        local dst = valuecells[version]
        if not dst then dst = {}; valuecells[version] = dst end
        unionset(dst, set)
    end

    for _, b in ipairs(out.cfg.blocks) do
        local state = copystate(instate[b.id])
        for _, pc in ipairs(b.pcs) do
            local op = out.proto.Instructions[pc]
            local name = ins.name(op)
            local uses = out.ssa.usesByPC[pc] or {}
            local defs = out.ssa.defsByPC[pc] or {}

            if name == "CAPTURE" and op.A == 1 then
                local set = state[op.B]
                if not set then set = {}; state[op.B] = set end
                set[capturecell[pc]] = true
            end

            for r, version in pairs(uses) do markvalue(version, state[r]) end
            for r, version in pairs(defs) do markvalue(version, state[r]) end

            if name == "CLOSEUPVALS" then
                for r, set in pairs(state) do
                    if r >= (op.A or 0) then
                        for cid in pairs(set) do
                            local list = closesites[cid]
                            if not list then list = {}; closesites[cid] = list end
                            list[pc] = true
                        end
                        state[r] = nil
                    end
                end
            end
        end
    end

    local parent = {}
    for cid = 1, nextcell - 1 do parent[cid] = cid end
    local function root(x)
        local p = parent[x]
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end
    local function join(a, b)
        a, b = root(a), root(b)
        if a ~= b then if a < b then parent[b] = a else parent[a] = b end end
    end
    local function joinset(set)
        local first
        for cid in pairs(set or {}) do if first then join(first, cid) else first = cid end end
    end
    for _, set in pairs(valuecells) do joinset(set) end
    for _, state in pairs(instate) do for _, set in pairs(state) do joinset(set) end end
    for _, state in pairs(outstate) do for _, set in pairs(state) do joinset(set) end end

    local cells, cellofvalue = {}, {}
    for pc, cid in pairs(capturecell) do
        local rid = root(cid)
        capturecell[pc] = rid
        local c = cells[rid]
        if not c then c = { id = rid, reg = capturereg[cid], captures = {}, closes = {}, values = {} }; cells[rid] = c end
        c.captures[#c.captures + 1] = pc
    end
    for version, set in pairs(valuecells) do
        local rid
        for cid in pairs(set) do rid = root(cid); break end
        if rid then
            cellofvalue[version] = rid
            local c = cells[rid]
            if not c then c = { id = rid, reg = capturereg[rid], captures = {}, closes = {}, values = {} }; cells[rid] = c end
            c.values[version] = true
        end
    end
    for cid, sites in pairs(closesites) do
        local rid = root(cid)
        local c = cells[rid]
        if c then for pc in pairs(sites) do c.closes[pc] = true end end
    end
    for _, c in pairs(cells) do table.sort(c.captures) end

    out.cells = cells
    out.cellOfValue = cellofvalue
    out.captureCell = capturecell
    out.cellInState = instate
    out.cellOutState = outstate
    out.cellIterations = iterations
    function out:cellId(valueid) return self.cellOfValue[valueid] or self.cellOfValue[self:resolve(valueid)] end
    return out
end

local function analyzeobjects(out, check)
    local sets, objects, nextobject = {}, {}, 1
    local function def(pc, reg)
        local d = out.ssa.defsByPC[pc]; return d and d[reg] or nil
    end
    local function use(pc, reg)
        local u = out.ssa.usesByPC[pc]; return u and u[reg] or nil
    end
    local function assign(id, nextset)
        if not id then return false end
        if not seteq(sets[id], nextset) then sets[id] = copyset(nextset); return true end
        return false
    end

    for _, n in ipairs(out.ops) do
        if n.name == "NEWTABLE" or n.name == "DUPTABLE" or n.name == "NEWCLASS" then
            local id = def(n.pc, n.op.A)
            if id then
                local oid = nextobject; nextobject += 1
                objects[oid] = { id = oid, allocPC = n.pc, kind = n.name, escaped = false, escapePCs = {}, aliases = {} }
                sets[id] = { [oid] = true }
            end
        end
    end

    local changed, iterations = true, 0
    local limit = math.max(32, #out.ops * 8 + 32)
    while changed do
        if check then check() end
        iterations += 1; if iterations > limit then error("LumenV4: ObjectId propagation failed to converge", 2) end
        changed = false
        for _, n in ipairs(out.ops) do
            if n.name == "MOVE" then
                changed = assign(def(n.pc, n.op.A), sets[use(n.pc, n.op.B)]) or changed
            elseif n.name == "NAMECALL" or n.name == "NAMECALLUDATA" then

                changed = assign(def(n.pc, n.op.A + 1), sets[use(n.pc, n.op.B)]) or changed
            end
        end
        for _, phis in pairs(out.phis) do
            for _, phi in pairs(phis) do
                local merged = {}
                for raw in pairs(phi.inputs or {}) do unionset(merged, sets[raw]) end
                changed = assign(phi.id, merged) or changed
            end
        end
    end

    local function mark(id, pc, reason)
        for oid in pairs(sets[id] or {}) do
            local obj = objects[oid]
            obj.escaped = true
            obj.escapePCs[pc] = reason or true
        end
    end


    for id, os in pairs(sets) do for oid in pairs(os) do objects[oid].aliases[id] = true end end
    for _, n in ipairs(out.ops) do
        local pc, op, name = n.pc, n.op, n.name
        local reads = out.ssa.usesByPC[pc] or {}
        local safebase = {}
        if name == "GETTABLE" or name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then safebase[op.B] = true
        elseif name == "SETTABLE" or name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then safebase[op.B] = true
        elseif name == "SETLIST" then safebase[op.A] = true
        elseif name == "NAMECALL" or name == "NAMECALLUDATA" then safebase[op.B] = true
        elseif name == "MOVE" then safebase[op.B] = true
        end

        for reg, id in pairs(reads) do
            if sets[id] and not safebase[reg] then
                local reason = name
                if name == "CALL" or name == "CALLFB" then reason = "CallUnknown"
                elseif name == "RETURN" then reason = "Return"
                elseif name == "CAPTURE" then reason = "Capture"
                elseif name == "SETGLOBAL" or name == "SETUPVAL" then reason = "StoreExternal"
                elseif name:match("^SETTABLE") or name == "SETUDATAKS" or name == "SETLIST" then reason = "StoreHeap" end
                mark(id, pc, reason)
            end
        end
    end

    out.objectSets = sets
    out.objects = objects
    out.objectIterations = iterations
    function out:objectIds(valueid) return self.objectSets[self:resolve(valueid)] or {} end
    function out:objectId(valueid)
        local one
        for oid in pairs(self:objectIds(valueid)) do if one then return nil end; one = oid end
        return one
    end
    return out
end

function build.run(proto, check, limits)
    local cfg = graph.build(proto, check, limits)
    local flow = ssa.build(proto, cfg, check, limits)
    assert(flow.converged, "LumenV4: refusing non-converged SSA")
    local out = fn.new(proto, cfg, flow)
    for id, src in ipairs(flow.versions) do
        out.vals[id] = val.new(id, src)
        if src.dead then out.dead[id] = true end
        if src.kind == "undef" then out.const[id] = "nil"; out.inline[id] = true end
    end
    for bid, phis in pairs(flow.phisByBlock) do
        local dst = {}; out.phis[bid] = dst
        for reg, p in pairs(phis) do
            dst[reg] = { id = p.id, reg = reg, inputs = p.inputs, incoming = p.incoming, missing = p.missing }
        end
    end
    for _, src in ipairs(cfg.blocks) do
        local b = block.new(src); out.blocks[b.id] = b
        for _, pc in ipairs(src.pcs) do
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local reads, writes, pack = regs.readWrite(op)
            local n = { pc = pc, op = op, name = name, block = b.id, reads = reads, writes = writes, pack = pack,
                pure = fx.pure(name), drop = fx.drop(name), quiet = fx.quiet(name), effect = fx.effect(name), term = fx.term(name) }
            out.ops[#out.ops + 1] = n; out.bypc[pc] = n; b.ops[#b.ops + 1] = n
        end
    end
    out:reindex()
    analyzecells(out, check)
    analyzeobjects(out, check)
    return out
end
return build
]===],
    ["main.ir.effects"] = [===[
local fx = {}

local relocatable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,

    MOVE = true,
}

local discardable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true, MOVE = true,
    NOT = true, AND = true, OR = true, ANDK = true, ORK = true,


}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, PREPVARARGS = true, COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

local effects = {
    GETGLOBAL = "ReadGlobal", SETGLOBAL = "WriteGlobal",
    GETUPVAL = "ReadCell", SETUPVAL = "WriteCell", CLOSEUPVALS = "CloseCells", CAPTURE = "CaptureCell",
    GETTABLE = "ReadTable", GETTABLEKS = "ReadTable", GETTABLEN = "ReadTable", GETUDATAKS = "ReadTable",
    SETTABLE = "WriteTable", SETTABLEKS = "WriteTable", SETTABLEN = "WriteTable", SETUDATAKS = "WriteTable",
    CALL = "CallUnknown", CALLFB = "CallUnknown", NAMECALL = "ReadTable", NAMECALLUDATA = "ReadTable",
    NEWCLOSURE = "AllocateClosure", DUPCLOSURE = "AllocateClosure",
    NEWTABLE = "AllocateObject", DUPTABLE = "AllocateObject", NEWCLASS = "AllocateObject", NEWCLASSMEMBER = "WriteTable",
    ADD = "MayMetamethod", SUB = "MayMetamethod", MUL = "MayMetamethod", DIV = "MayMetamethod", MOD = "MayMetamethod",
    POW = "MayMetamethod", IDIV = "MayMetamethod", ADDK = "MayMetamethod", SUBK = "MayMetamethod", MULK = "MayMetamethod",
    DIVK = "MayMetamethod", MODK = "MayMetamethod", POWK = "MayMetamethod", IDIVK = "MayMetamethod",
    SUBRK = "MayMetamethod", DIVRK = "MayMetamethod", CONCAT = "MayMetamethod", LENGTH = "MayMetamethod",
    GETIMPORT = "ReadImport", NATIVECALL = "CallUnknown",
}

function fx.pure(name) return relocatable[name] == true end
function fx.drop(name) return discardable[name] == true end
function fx.quiet(name) return quiet[name] == true end
function fx.term(name) return term[name] == true end
function fx.class(name)
    if term[name] then return "Control" end
    return effects[name] or (quiet[name] and "Pure" or "Unknown")
end
function fx.effect(name)
    local c = fx.class(name)
    return c ~= "Pure" and c ~= "Control"
end
function fx.canRelocate(name) return relocatable[name] == true end

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

    if self.opt.smartnames == false then
        if pc == 1 and reg < (self.proto.ParameterCount or 0) then return self:unique("arg" .. tostring(reg + 1)) end
        return self:name(reg, nil)
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
    if self.opt.smartnames ~= false and hint and self:stable(reg) then base = id.clean(hint) end
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

function pass.run(ir, check)
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
        if check then check() end
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
    ["main.passes.inline"] = [===[local ins = require("main.bytecode.instructions")

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

local function mutablevalues(ir, check)
    local mutable = {}
    local changed = true


    for id, objectset in pairs(ir.objectSets or {}) do
        if next(objectset) then
            local resolved = ir:resolve(id)
            if resolved then mutable[resolved] = true end
        end
    end

    for _, n in ipairs(ir.ops) do
        if n.name == "NEWTABLE" or n.name == "DUPTABLE" or n.name == "NEWCLASS" then
            local defs = ir.ssa.defsByPC[n.pc] or {}
            local v = ir:resolve(defs[n.op.A])
            if v then mutable[v] = true end
        end
    end

    while changed do
        if check then check() end
        changed = false
        for _, n in ipairs(ir.ops) do
            if n.name == "MOVE" then
                local uses = ir.ssa.usesByPC[n.pc] or {}
                local defs = ir.ssa.defsByPC[n.pc] or {}
                local src = ir:resolve(uses[n.op.B])
                local dst = ir:resolve(defs[n.op.A])
                if src and dst and mutable[src] and not mutable[dst] then mutable[dst] = true; changed = true end
            end
        end
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                local pid = ir:resolve(p.id)
                if pid and not mutable[pid] then
                    for raw in pairs(p.inputs or {}) do
                        local src = ir:resolve(raw)
                        if src and mutable[src] then mutable[pid] = true; changed = true break end
                    end
                end
            end
        end
    end
    return mutable
end

function pass.run(ir, check)
    local mutable = mutablevalues(ir, check)
    ir.mutableObjects = mutable

    for id, v in pairs(ir.vals) do
        if check then check() end
        id = ir:resolve(id)
        if id and not ir.dead[id] and v.kind == "def" and not mutable[id] then
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
        id = ir:resolve(id)
        if id and not mutable[id] then
            local ok = ir:count(id) > 0
            for _, u in ipairs(ir:uses(id) or {}) do
                local useop = u.pc and ir.bypc[u.pc] or nil
                if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
            end
            if ok then ir.inline[id] = true end
        end
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

local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt, check)
    opt = opt or {}


    if check then check() end
    if opt.dce ~= false then dead.run(ir, check) end
    if check then check() end


    names.run(ir)
    if check then check() end
    if opt.smartnames ~= false then
        prov.run(ir)
        if check then check() end
    else
        ir.bestname, ir.namescore, ir.hints, ir.origin = {}, {}, {}, {}
    end

    if opt.inline ~= false then inline.run(ir, check) end
    if check then check() end
    cond.run(ir)
    if check then check() end
    flow.run(ir)
    if check then check() end
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
    ["main.recover.branches"] = [===[local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end

    local join = st:join(pc)

    if not join or join <= pc or join > stop then return nil end
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
    ["main.recover.functions"] = [===[local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local fn = {}

local evt = {
    PlayerAdded = { "player" }, PlayerRemoving = { "player" }, CharacterAdded = { "character" }, CharacterRemoving = { "character" },
    ChildAdded = { "child" }, ChildRemoved = { "child" }, DescendantAdded = { "descendant" }, DescendantRemoving = { "descendant" },
    Touched = { "hit" }, TouchEnded = { "hit" }, InputBegan = { "input", "gameProcessed" }, InputChanged = { "input", "gameProcessed" },
    InputEnded = { "input", "gameProcessed" }, Heartbeat = { "dt" }, RenderStepped = { "dt" }, PreRender = { "dt" },
    PreSimulation = { "dt" }, PostSimulation = { "dt" }, Stepped = { "time", "dt" }, AncestryChanged = { "child", "parent" },
    AttributeChanged = { "attribute" }, Changed = { "value" },
}
local meth = { BindToRenderStep = { "dt" }, BindAction = { "actionName", "inputState", "input" }, BindActionAtPriority = { "actionName", "inputState", "input" } }

local function cbhints(st, pc, r)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local call
    for _, u in ipairs(st.ir:uses(v) or {}) do if u.pc then if call then return nil end; call = u.pc end end
    if not call then return nil end
    local op = st.proto.Instructions[call]
    local name = ins.name(op)
    if name ~= "CALL" and name ~= "CALLFB" then return nil end
    local pend = st.namecall[op.A]
    if pend and (pend.method == "Connect" or pend.method == "ConnectParallel" or pend.method == "Once") then
        local tail = pend.obj and pend.obj:match("([%a_][%w_]*)$")
        return tail and evt[tail] or nil
    end
    return pend and meth[pend.method] or nil
end

local function capturename(st, cp, kind, src, debugname)


    local parent
    if kind == 0 or kind == 1 then
        parent = st:useName(cp, src, nil)
    else
        parent = st.up[src + 1] or ("upvalue" .. tostring(src))
    end
    if not parent or parent == "" then parent = debugname end
    return parent or ("upvalue" .. tostring(src))
end

function fn.caps(st, pc, child)
    local out = {}
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        local du = child.Upvalues and child.Upvalues[i]
        local dn = du and du.Name
        if not op or ins.name(op) ~= "CAPTURE" then
            error(("LumenV4: UNSUPPORTED NEWCLOSURE at pc %d expected CAPTURE %d/%d"):format(pc, i, child.UpvalueCount or 0), 2)
        end

        local kind, src = op.A, op.B
        if kind ~= 0 and kind ~= 1 and kind ~= 2 then
            error(("LumenV4: UNSUPPORTED CAPTURE kind %s at pc %d"):format(tostring(kind), cp), 2)
        end
        if kind == 0 or kind == 1 then
            if not st:veruse(cp, src) then
                error(("LumenV4: UNSUPPORTED CAPTURE references undefined parent register R%d at pc %d"):format(src, cp), 2)
            end
        elseif not st.up[src + 1] then
            error(("LumenV4: UNSUPPORTED CAPTURE_UPVAL references missing parent upvalue U%d at pc %d"):format(src, cp), 2)
        end

        if kind == 0 then


            local snap = st.naming:unique("capture" .. tostring(i) .. "Value")
            st.declared[snap] = st.indent
            st:out("local " .. snap .. " = " .. st:use(cp, src))
            out[i] = snap
        else
            out[i] = capturename(st, cp, kind, src, dn)
        end
        st.consumed[cp] = true
        nx = st:next(cp)
    end
    local extra = st.proto.Instructions[nx]
    if extra and ins.name(extra) == "CAPTURE" then
        error(("LumenV4: UNSUPPORTED NEWCLOSURE at pc %d has more CAPTURE instructions than child upvalues"):format(pc), 2)
    end
    return out, nx
end

local function direct(st, pc, r, nx)
    local v = st:verdef(pc, r)
    if not v then return nil end
    local uses, one = st.ir:uses(v) or {}, nil
    for _, u in ipairs(uses) do if u.pc then if one then return nil end; one = u end end
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
        if not assign and target:find("%.") and args[1] and (args[1]:match("^self%s*[:$]") or args[1] == "self") then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then target = base .. ":" .. field; table.remove(args, 1) end
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

local paths = {
    "Src/init.luau",
    "Src/Deserializer.d.luau",
    "Src/Utilities/Buffer.luau",
    "Src/Luau/Spec.luau",
    "Src/Luau/TypeInfo.luau",
    "Src/Classes/Proto.luau",
    "Src/Classes/Instructions.luau",
    "Src/Classes/Instruction.luau",
    "Src/Classes/Hexadecimal.luau",
    "Src/Classes/Upvalue.luau",
    "Src/Classes/Constants/Nil.luau",
    "Src/Classes/Constants/Boolean.luau",
    "Src/Classes/Constants/Number.luau",
    "Src/Classes/Constants/String.luau",
    "Src/Classes/Constants/Import.luau",
    "Src/Classes/Constants/Table.luau",
    "Src/Classes/Constants/Closure.luau",
    "Src/Classes/Constants/Vector.luau",
    "Src/Classes/Constants/TableWithConstants.luau",
    "Src/Classes/Constants/Integer.luau",
    "Src/Classes/Constants/ClassShape.luau",
}

local cache = {}
local srcs = {}
local NIL = {}
local LOADING = {}
local root = nil
local loading = false
local loaderr = nil
local warming = false
local warmed = false
local warmerr = nil

local e = env.get()
local vend = rawget(e, "__LUMEN_IRIDIUM_VENDOR")
if type(vend) == "table" then
    for k, v in pairs(vend) do
        if type(k) == "string" and type(v) == "string" then srcs[k] = v end
    end
end

local function resolve(name)
    if name == "@root" then return "Src/init.luau" end
    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end
    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local function fetch(path)
    local src = srcs[path]
    if src then return src end
    src = http.get(rawBase .. path)
    srcs[path] = src
    return src
end

function iri.prefetch()
    if warmed then return true end
    if warming then
        while warming do task.wait() end
        if warmerr then return false, warmerr end
        return true
    end

    warming = true
    warmerr = nil
    local left = 0
    local errs = {}

    for _, path in ipairs(paths) do
        if not srcs[path] then
            left += 1
            task.spawn(function()
                local ok, val = pcall(http.get, rawBase .. path)
                if ok and type(val) == "string" and val ~= "" then
                    srcs[path] = val
                else
                    errs[#errs + 1] = path .. ": " .. tostring(val)
                end
                left -= 1
            end)
        end
    end

    while left > 0 do task.wait() end
    warming = false
    if #errs > 0 then
        warmerr = table.concat(errs, " | ")
        return false, warmerr
    end
    warmed = true
    return true
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
        local src = patch.apply(path, fetch(path))
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
    if root then return root end
    if loading then
        while loading do task.wait() end
        if root then return root end
        error(loaderr or "LumenDecomp: Iridium load failed", 2)
    end

    loading = true
    loaderr = nil
    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)
    e[key] = req
    local ok, value = pcall(req, "@root")
    if old == nil then e[key] = nil else e[key] = old end

    if not ok then
        loading = false
        loaderr = tostring(value)
        error(value, 2)
    end

    if type(value) ~= "table" or type(value.Deserialize) ~= "function" then
        loading = false
        loaderr = "LumenDecomp: Iridium root did not expose Deserialize"
        error(loaderr, 2)
    end

    root = value
    loading = false
    return root
end

function iri.warm()
    iri.prefetch()
    local rok, val = pcall(iri.get)
    if not rok then return false, tostring(val) end
    return true
end

local function lit(s)
    for n = 3, 12 do
        local eq = string.rep("=", n)
        local close = "]" .. eq .. "]"
        if not s:find(close, 1, true) then
            return "[" .. eq .. "[" .. s .. close
        end
    end
    return string.format("%q", s)
end

function iri.pack()
    iri.prefetch()
    for _, path in ipairs(paths) do
        if not srcs[path] then
            local ok, val = pcall(fetch, path)
            if not ok then return nil, tostring(val) end
        end
    end
    local out = { "return {" }
    for _, path in ipairs(paths) do
        out[#out + 1] = "[" .. string.format("%q", path) .. "]=" .. lit(srcs[path]) .. ","
    end
    out[#out + 1] = "}"
    return table.concat(out)
end

function iri.info()
    local pi = patch.info()
    local n = 0
    for _ in pairs(srcs) do n += 1 end
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
        prefetched = n,
        vendor = type(vend) == "table",
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
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:warm()
    local ok, err = iri.warm()
    if not ok then error(err, 2) end
    return true
end

function worker:decompileBytecode(raw, opt)
    opt = cfg(opt)
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
    MaxPathLength = rawget(_G, "MaxPathLength"),
    AcquireBatch = rawget(_G, "AcquireBatch"),
    AcquireBudgetMs = rawget(_G, "AcquireBudgetMs"),
    DecompilerOptions = rawget(_G, "DecompilerOptions"),
    SmartVariableRenamer = rawget(_G, "SmartVariableRenamer"),
    FunctionDeclarations = rawget(_G, "FunctionDeclarations"),
    GuardClauses = rawget(_G, "GuardClauses"),
    ConstantFolding = rawget(_G, "ConstantFolding"),
    ConditionalStructurer = rawget(_G, "ConditionalStructurer"),
    DoBlockInsertionThreshold = rawget(_G, "DoBlockInsertionThreshold"),
}
if type(getgenv) == "function" then
    local ok, e = pcall(getgenv)
    if ok and type(e) == "table" then
        for _, k in ipairs({ "Binary", "Decompile", "Tree", "IgnoreCoreScripts", "Parallel", "MaxWorkers", "MaxPathLength", "AcquireBatch", "AcquireBudgetMs", "DecompilerOptions", "SmartVariableRenamer", "FunctionDeclarations", "GuardClauses", "ConstantFolding", "ConditionalStructurer", "DoBlockInsertionThreshold" }) do
            if boot[k] == nil then boot[k] = rawget(e, k) end
        end
    end
end
api:auto(boot)
return api
