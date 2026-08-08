local ins = require("main.bytecode.instructions")
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
