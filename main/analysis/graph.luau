local ins = require("main.bytecode.instructions")
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
