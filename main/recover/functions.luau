local ins = require("main.bytecode.instructions")

local fn = {}

function fn.caps(st, pc, child)
    local out = {}
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        if ins.name(op) ~= "CAPTURE" then
            out[i] = "upvalue" .. tostring(i - 1)
        else
            local kind, src = op.A, op.B
            if kind == 0 or kind == 1 then out[i] = st:useName(cp, src, nil)
            else out[i] = st.up[src + 1] or ("upvalue" .. tostring(src)) end
            st.consumed[cp] = true
            nx = st:next(cp)
        end
    end
    return out
end

function fn.emit(d, st, pc, r, child, caps)
    local hint = child.Name
    if hint == nil or hint == "" then hint = "fn" .. tostring(r) end
    local name = st:defName(pc, r, hint)
    local root, sub, args = d:_child(child, caps)
    local depth = st.declared[name]
    if depth == nil or depth > st.indent then
        st.declared[name] = st.indent
        st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = true, assign = false })
    else
        st.ast:add({ kind = "function", name = name, args = table.concat(args, ", "), body = root, localfn = false, assign = true })
    end
    for _, issue in ipairs(sub.bad) do st.bad[#st.bad + 1] = issue end
end

return fn
