
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
