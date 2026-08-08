local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")

local tab = {}

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
        if e.kind == "list" then
            out[#out + 1] = ex.str(e.val)
        elseif e.kind == "field" then
            out[#out + 1] = e.key .. " = " .. ex.str(e.val)
        else
            out[#out + 1] = "[" .. e.key .. "] = " .. ex.str(e.val)
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
