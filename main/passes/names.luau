local pass = {}

local function copyset(src)
    local out = {}
    for k in pairs(src or {}) do out[k] = true end
    return out
end

local function seteq(a, b)
    a, b = a or {}, b or {}
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end

local function union(dst, src)
    for k in pairs(src or {}) do dst[k] = true end
end

local function addpair(graph, a, b)
    if not a or not b or a == b then return end
    local ga = graph[a]
    if not ga then ga = {}; graph[a] = ga end
    local gb = graph[b]
    if not gb then gb = {}; graph[b] = gb end
    ga[b] = true
    gb[a] = true
end

local function cellmap(ir)
    local out = {}
    for raw, set in pairs(ir.cellSetsByValue or {}) do
        local id = ir:resolve(raw)
        if id then
            local count, only = 0, nil
            for cid in pairs(set or {}) do count += 1; only = cid end
            local marker = count == 1 and only or (count > 1 and ("multi:" .. tostring(id)) or nil)
            if marker then
                local old = out[id]
                if old and old ~= marker then
                    error(("LumenV4: SSA_DESTRUCT value v%d aliases incompatible CellIds %s/%s"):format(id, tostring(old), tostring(marker)), 2)
                end
                out[id] = marker
            end
        end
    end
    for raw, cid in pairs(ir.cellOfValue or {}) do
        local id = ir:resolve(raw)
        if id and out[id] == nil then out[id] = cid end
    end
    return out
end

local function buildliveness(ir)
    local cfg = ir.cfg
    local use, def, phidef, edgeuse = {}, {}, {}, {}

    for _, block in ipairs(cfg.blocks) do
        local bid = block.id
        local u, d, pd = {}, {}, {}
        local phis = ir.phis[bid]
        if phis then
            for _, phi in pairs(phis) do
                local id = ir:resolve(phi.id)
                if id and not ir.dead[id] and ir:count(id) > 0 then
                    d[id] = true
                    pd[id] = true
                end
            end
        end

        for _, pc in ipairs(block.pcs) do
            local uses = ir.ssa.usesByPC[pc]
            if uses then
                for _, raw in pairs(uses) do
                    local id = ir:resolve(raw)
                    if id and not ir.dead[id] and not d[id] then u[id] = true end
                end
            end
            local defs = ir.ssa.defsByPC[pc]
            if defs then
                for _, raw in pairs(defs) do
                    local id = ir:resolve(raw)
                    if id and not ir.dead[id] then d[id] = true end
                end
            end
        end
        use[bid], def[bid], phidef[bid] = u, d, pd
    end

    for succ, phis in pairs(ir.phis) do
        for _, phi in pairs(phis) do
            local dst = ir:resolve(phi.id)
            if dst and not ir.dead[dst] and ir:count(dst) > 0 then
                for pred, raw in pairs(phi.incoming or {}) do
                    local id = ir:resolve(raw)
                    if id and not ir.dead[id] then
                        local bypred = edgeuse[pred]
                        if not bypred then bypred = {}; edgeuse[pred] = bypred end
                        local set = bypred[succ]
                        if not set then set = {}; bypred[succ] = set end
                        set[id] = true
                    end
                end
            end
        end
    end

    local lin, lout = {}, {}
    for _, block in ipairs(cfg.blocks) do lin[block.id], lout[block.id] = {}, {} end

    local changed, iterations = true, 0
    local limit = math.max(64, #cfg.blocks * 512)
    while changed do
        iterations += 1
        if iterations > limit then error("LumenV4: SSA_DESTRUCT liveness failed to converge", 2) end
        changed = false
        for i = #cfg.blocks, 1, -1 do
            local block = cfg.blocks[i]
            local bid = block.id
            local out = {}
            for _, succ in ipairs(block.successors) do
                local sin = lin[succ] or {}
                local spd = phidef[succ] or {}
                for id in pairs(sin) do if not spd[id] then out[id] = true end end
                local eu = edgeuse[bid] and edgeuse[bid][succ]
                union(out, eu)
            end
            local inn = copyset(use[bid])
            for id in pairs(out) do if not def[bid][id] then inn[id] = true end end
            if not seteq(lout[bid], out) then lout[bid] = out; changed = true end
            if not seteq(lin[bid], inn) then lin[bid] = inn; changed = true end
        end
    end

    return {
        use = use,
        def = def,
        phiDef = phidef,
        edgeUse = edgeuse,
        liveIn = lin,
        liveOut = lout,
        iterations = iterations,
    }
end

local function interference(ir, live)
    local graph = {}
    for id in pairs(ir.vals) do graph[id] = graph[id] or {} end

    for _, block in ipairs(ir.cfg.blocks) do
        local now = copyset(live.liveOut[block.id])

        for i = #block.pcs, 1, -1 do
            local pc = block.pcs[i]
            local defs = {}
            for _, raw in pairs(ir.ssa.defsByPC[pc] or {}) do
                local id = ir:resolve(raw)
                if id and not ir.dead[id] then defs[id] = true end
            end
            for d in pairs(defs) do
                for v in pairs(now) do addpair(graph, d, v) end
            end
            for d in pairs(defs) do now[d] = nil end
            for _, raw in pairs(ir.ssa.usesByPC[pc] or {}) do
                local id = ir:resolve(raw)
                if id and not ir.dead[id] then now[id] = true end
            end
        end

        local phis = ir.phis[block.id]
        if phis then
            local pdefs, incoming = {}, {}
            for _, phi in pairs(phis) do
                local d = ir:resolve(phi.id)
                if d and not ir.dead[d] and ir:count(d) > 0 then
                    pdefs[d] = true
                    for _, raw in pairs(phi.incoming or {}) do
                        local id = ir:resolve(raw)
                        if id then incoming[id] = true end
                    end
                end
            end
            for d in pairs(pdefs) do
                for v in pairs(now) do
                    if not incoming[v] then addpair(graph, d, v) end
                end
                for other in pairs(pdefs) do addpair(graph, d, other) end
            end
        end
    end

    return graph
end

local function coalesce(ir, graph, cells)
    local parent, members, groupcell = {}, {}, {}

    for id in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not parent[id] then
            parent[id] = id
            members[id] = { [id] = true }
            groupcell[id] = cells[id]
        end
    end

    local function root(x)
        x = ir:resolve(x)
        if not x then return nil end
        local p = parent[x]
        if not p then
            parent[x], members[x], groupcell[x] = x, { [x] = true }, cells[x]
            return x
        end
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end

    local function compatible(a, b)
        local ca, cb = groupcell[a], groupcell[b]
        return ca == cb or (ca == nil and cb == nil)
    end

    local function conflicts(a, b)
        for x in pairs(members[a]) do
            local gx = graph[x]
            if gx then
                for y in pairs(members[b]) do if gx[y] then return true end end
            end
        end
        return false
    end

    local function join(a, b)
        a, b = root(a), root(b)
        if not a or not b or a == b then return true end
        local av, bv = ir.vals[a], ir.vals[b]
        if (av and av.kind == "undef") or (bv and bv.kind == "undef") then return false end
        if not compatible(a, b) or conflicts(a, b) then return false end
        local keep, drop = a, b
        if drop < keep then keep, drop = drop, keep end
        parent[drop] = keep
        for id in pairs(members[drop]) do members[keep][id] = true end
        members[drop] = nil
        groupcell[keep] = groupcell[keep] or groupcell[drop]
        groupcell[drop] = nil
        return true
    end

    local candidates = {}
    for bid, phis in pairs(ir.phis) do
        for reg, phi in pairs(phis) do
            local dst = ir:resolve(phi.id)
            if dst and not ir.dead[dst] and ir:count(dst) > 0 then
                local preds = {}
                for pred in pairs(phi.incoming or {}) do preds[#preds + 1] = pred end
                table.sort(preds)
                for _, pred in ipairs(preds) do
                    local src = ir:resolve(phi.incoming[pred])
                    if src and not ir.dead[src] then
                        candidates[#candidates + 1] = { kind = "phi", dst = dst, src = src, bid = bid, pred = pred, reg = reg }
                    end
                end
            end
        end
    end

    for _, n in ipairs(ir.ops or {}) do
        if n.name == "MOVE" then
            local dst = ir:def(n.pc, n.op.A)
            local src = ir:use(n.pc, n.op.B)
            if dst and src and dst ~= src then
                candidates[#candidates + 1] = { kind = "move", dst = dst, src = src, pc = n.pc }
            end
        end
    end

    table.sort(candidates, function(a, b)
        if a.kind ~= b.kind then return a.kind == "phi" end
        local ap, bp = a.pc or (a.bid * 65536 + a.pred), b.pc or (b.bid * 65536 + b.pred)
        return ap < bp
    end)

    local merged = 0
    for _, c in ipairs(candidates) do if join(c.dst, c.src) then merged += 1 end end

    local family = {}
    for id in pairs(ir.vals) do
        local rid = ir:resolve(id)
        if rid then family[id] = root(rid) end
    end

    return family, root, members, merged
end

local function buildcopies(ir, family)
    local edge = {}
    local count = 0

    for succ, phis in pairs(ir.phis) do
        local block = ir.cfg.blocks[succ]
        if block then
            for reg, phi in pairs(phis) do
                local dst = ir:resolve(phi.id)
                if dst and not ir.dead[dst] and ir:count(dst) > 0 then
                    local df = family[dst] or dst
                    for _, pred in ipairs(block.predecessors) do
                        local raw = phi.incoming and phi.incoming[pred]
                        local src = raw and ir:resolve(raw) or nil
                        local sf = src and (family[src] or src) or nil
                        if sf ~= df then
                            local bypred = edge[pred]
                            if not bypred then bypred = {}; edge[pred] = bypred end
                            local list = bypred[succ]
                            if not list then list = {}; bypred[succ] = list end
                            list[#list + 1] = {
                                dst = df,
                                src = sf,
                                dstValue = dst,
                                srcValue = src,
                                reg = reg,
                                phi = phi.id,
                                undef = src and ir.vals[src] and ir.vals[src].kind == "undef" or src == nil,
                            }
                            count += 1
                        end
                    end
                end
            end
        end
    end

    for _, bysucc in pairs(edge) do
        for _, list in pairs(bysucc) do
            table.sort(list, function(a, b)
                if a.reg ~= b.reg then return a.reg < b.reg end
                return (a.dst or 0) < (b.dst or 0)
            end)
        end
    end
    return edge, count
end

local function verify(ir, outssa)
    local family = outssa.family
    local graph = outssa.interference
    local cells = outssa.cells

    local seenfamilies = {}
    for id in pairs(ir.vals) do
        local rid = ir:resolve(id)
        if rid and family[rid] then
            local f = family[rid]
            local list = seenfamilies[f]
            if not list then list = {}; seenfamilies[f] = list end
            list[#list + 1] = rid
        end
    end

    for _, list in pairs(seenfamilies) do
        local cell
        for i = 1, #list do
            local a = list[i]
            local ca = cells[a]
            if ca then
                if cell and cell ~= ca then error("LumenV4: SSA_DESTRUCT coalesced distinct CellIds", 2) end
                cell = ca
            end
            for j = i + 1, #list do
                local b = list[j]
                if graph[a] and graph[a][b] then
                    error(("LumenV4: SSA_DESTRUCT coalesced interfering values v%d/v%d"):format(a, b), 2)
                end
            end
        end
    end

    for succ, phis in pairs(ir.phis) do
        local block = assert(ir.cfg.blocks[succ], "LumenV4: SSA_DESTRUCT phi block missing")
        for reg, phi in pairs(phis) do
            local dst = ir:resolve(phi.id)
            if dst and not ir.dead[dst] and ir:count(dst) > 0 then
                for _, pred in ipairs(block.predecessors) do
                    local raw = phi.incoming and phi.incoming[pred]
                    if raw == nil and not phi.missing then
                        error(("LumenV4: SSA_DESTRUCT phi v%d r%d missing predecessor b%d"):format(dst, reg, pred), 2)
                    end
                    local src = raw and ir:resolve(raw) or nil
                    local df = family[dst] or dst
                    local sf = src and (family[src] or src) or nil
                    if sf ~= df then
                        local found = false
                        for _, copy in ipairs(outssa.edgeCopies[pred] and outssa.edgeCopies[pred][succ] or {}) do
                            if copy.dst == df and copy.src == sf and copy.reg == reg then found = true break end
                        end
                        if not found then
                            error(("LumenV4: SSA_DESTRUCT missing edge copy b%d->b%d r%d"):format(pred, succ, reg), 2)
                        end
                    end
                end
            end
        end
    end

    return true
end

function pass.run(ir)
    local live = buildliveness(ir)
    local cells = cellmap(ir)
    local graph = interference(ir, live)
    local family, _, members, merged = coalesce(ir, graph, cells)
    local copies, copycount = buildcopies(ir, family)

    local materialize = {}
    for _, bysucc in pairs(copies) do
        for _, list in pairs(bysucc) do
            for _, copy in ipairs(list) do
                if copy.dst then materialize[copy.dst] = true end
                if copy.src and not copy.undef then materialize[copy.src] = true end
            end
        end
    end
    for id, fam in pairs(family) do if materialize[fam] then materialize[id] = true end end

    ir.family = family
    ir.outssa = {
        liveIn = live.liveIn,
        liveOut = live.liveOut,
        edgeUse = live.edgeUse,
        livenessIterations = live.iterations,
        interference = graph,
        cells = cells,
        members = members,
        family = family,
        edgeCopies = copies,
        copyCount = copycount,
        coalesced = merged,
        materialize = materialize,
        verified = false,
    }
    ir.outssa.verified = verify(ir, ir.outssa)
    return ir
end

return pass
