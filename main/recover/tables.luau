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

local function sameobject(st, value, oid)
    if not value or not oid or not st.ir.objectId then return false end
    return st.ir:objectId(value) == oid
end

local function mutation(st, pc, oid)
    local op = st.proto.Instructions[pc]
    if not op then return false end
    local name = ins.name(op)
    local uses = st.ssa.usesByPC[pc] or {}
    local base
    if name == "SETTABLE" or name == "SETTABLEKS" or name == "SETUDATAKS" or name == "SETTABLEN" then base = uses[op.B]
    elseif name == "SETLIST" then base = uses[op.A]
    else return false end
    if not sameobject(st, base, oid) then return false end

    if name == "SETTABLE" then
        if sameobject(st, uses[op.A], oid) or sameobject(st, uses[op.C], oid) then return false, "self" end
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" or name == "SETTABLEN" then
        if sameobject(st, uses[op.A], oid) then return false, "self" end
    elseif name == "SETLIST" then
        local _, _, pack = require("main.analysis.registers").readWrite(op)
        if op.C == 0 and pack.openReadFrom then return false, "open" end
        local last = op.C > 1 and (op.B + op.C - 2) or (op.B - 1)
        for r = op.B, last do if sameobject(st, uses[r], oid) then return false, "self" end end
    end
    return true
end

local function linear(cfg, first, second)
    if first == second then return true end
    local seen = {}
    local cur = first
    while cur and not seen[cur] do
        seen[cur] = true
        local b = cfg.blocks[cur]
        if not b or #b.successors ~= 1 then return false end
        local nx = b.successors[1]
        local nb = cfg.blocks[nx]
        if not nb or #nb.predecessors ~= 1 or nb.predecessors[1] ~= cur then return false end
        if nx == second then return true end
        cur = nx
    end
    return false
end

function tab.get(st, value)
    if not value then return nil end
    local direct = st.tbl[value]
    if direct then return direct end
    local oid = st.ir.objectId and st.ir:objectId(value)
    return oid and st.tblobj and st.tblobj[oid] or nil
end

function tab.begin(st, pc, reg, seed, slots)
    local value = st:verdef(pc, reg)
    if not value or not st.ir.objectId then return nil end
    local oid = st.ir:objectId(value)
    if not oid then return nil end
    local object = st.ir.objects and st.ir.objects[oid]
    if not object or object.allocPC ~= pc then return nil end

    local t = {
        oid = oid,
        value = value,
        reg = reg,
        entries = seed or {},
        slots = slots,
        real = 0,
        done = false,
        allowed = {},
        allocPC = pc,
        object = object,
    }

    local uses = {}
    for alias in pairs(object.aliases or {}) do
        for _, use in ipairs(st.ir:uses(alias) or {}) do
            if use.pc and use.pc > pc then uses[use.pc] = true end
        end
    end
    local pcs = {}
    for upc in pairs(uses) do pcs[#pcs + 1] = upc end
    table.sort(pcs)

    local allocblock = st.cfg.blockmap[pc]
    local lastblock = allocblock
    local observed = false
    for _, upc in ipairs(pcs) do
        local ub = st.cfg.blockmap[upc]
        local ok, why = mutation(st, upc, oid)
        if ok and not observed and ub and linear(st.cfg, lastblock, ub) then
            t.allowed[upc] = true
            lastblock = ub
        else
            local op = st.proto.Instructions[upc]
            local name = op and ins.name(op)
            if name ~= "MOVE" and not (ok and why == nil) then
                observed = true
                t.real += 1
            elseif not ok then
                observed = true
                t.real += 1
            end
        end
    end

    st.tblobj = st.tblobj or {}
    st.tblobj[oid] = t
    st.tbl[value] = t
    return t
end

function tab.canput(t, pc)
    return t and not t.done and t.allowed and t.allowed[pc] == true
end

function tab.expr(t)
    local fields = {}
    for _, e in ipairs(t.entries) do
        if not e.pending and e.val then
            fields[#fields + 1] = { kind = e.kind, key = e.key, value = e.val }
        end
    end
    return ex.table(fields)
end

function tab.use(st, v, r, pc)
    local t = tab.get(st, v)
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
