local graph = require("main.analysis.graph")
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
