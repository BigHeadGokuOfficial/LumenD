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

local function valuecap(st, cp, src, slot, debugname, selfreg)
    local raw = st:veruse(cp, src)
    if not raw then
        error(("LumenV4: CAPTURE_VERIFY value capture references undefined parent register R%d at pc %d"):format(src, cp), 2)
    end
    local value = st.ir:resolve(raw)
    if src == selfreg then
        return {
            kind = "self",
            mode = 0,
            value = value,
            reg = src,
            pc = cp,
            slot = slot,
            owner = st,
            debugname = debugname,
        }
    end
    local snap = st.naming:unique("capture" .. tostring(slot) .. "Value")
    st.declared[snap] = st.indent
    st:out("local " .. snap .. " = " .. st:use(cp, src))
    return {
        kind = "value",
        mode = 0,
        value = value,
        reg = src,
        pc = cp,
        slot = slot,
        owner = st,
        name = snap,
        debugname = debugname,
    }
end

local function refcap(st, cp, src, slot, debugname)
    local raw = st:veruse(cp, src)
    if not raw then
        error(("LumenV4: CAPTURE_VERIFY ref capture references undefined parent register R%d at pc %d"):format(src, cp), 2)
    end
    local value = st.ir:resolve(raw)
    local cell = st.ir.captureCell and st.ir.captureCell[cp]
    if not cell and st.ir.cellOfValue then cell = st.ir.cellOfValue[raw] or st.ir.cellOfValue[value] end
    if not cell then
        error(("LumenV4: CAPTURE_VERIFY REF capture has no CellId for R%d at pc %d"):format(src, cp), 2)
    end
    local name
    if st.dispatchCells then
        local box = st.dispatchCells .. "[" .. tostring(cell) .. "]"
        local base = st:dispatchbase(value, src, cp)
        st:out("if " .. box .. " == nil then " .. box .. " = {v = " .. base .. "} end")
        local snap = st.naming:unique("capture" .. tostring(slot) .. "Cell")
        st.declared[snap] = st.indent
        st:out("local " .. snap .. " = " .. box)
        name = snap .. ".v"
    end
    return {
        kind = "ref",
        mode = 1,
        value = value,
        cell = cell,
        reg = src,
        pc = cp,
        slot = slot,
        owner = st,
        name = name,
        debugname = debugname,
    }
end

local function upcap(st, cp, src, slot, debugname)
    local parent = st:updesc(src + 1)
    if not parent then
        error(("LumenV4: CAPTURE_VERIFY UPVAL capture references missing parent upvalue U%d at pc %d"):format(src, cp), 2)
    end
    return {
        kind = "upvalue",
        mode = 2,
        parent = parent,
        cell = st:upcell(src + 1),
        source = src,
        pc = cp,
        slot = slot,
        owner = st,
        debugname = debugname,
    }
end

function fn.verify(child, caps, pc)
    local want = child.UpvalueCount or 0
    if #caps ~= want then
        error(("LumenV4: CAPTURE_VERIFY NEWCLOSURE at pc %d capture slot mismatch %d/%d"):format(pc, #caps, want), 2)
    end
    for i = 1, want do
        local cap = caps[i]
        if type(cap) ~= "table" then
            error(("LumenV4: CAPTURE_VERIFY slot %d at pc %d is not semantic"):format(i, pc), 2)
        end
        if cap.slot ~= i then
            error(("LumenV4: CAPTURE_VERIFY slot index mismatch %d/%s at pc %d"):format(i, tostring(cap.slot), pc), 2)
        end
        if cap.kind == "self" then
            if not cap.value or not cap.name then
                error(("LumenV4: CAPTURE_VERIFY recursive value slot %d at pc %d has no function identity"):format(i, pc), 2)
            end
        elseif cap.kind == "value" then
            if not cap.value or not cap.name then
                error(("LumenV4: CAPTURE_VERIFY value slot %d at pc %d has no snapshot identity"):format(i, pc), 2)
            end
        elseif cap.kind == "ref" then
            if not cap.cell then
                error(("LumenV4: CAPTURE_VERIFY ref slot %d at pc %d has no CellId"):format(i, pc), 2)
            end
        elseif cap.kind == "upvalue" then
            if not cap.parent then
                error(("LumenV4: CAPTURE_VERIFY inherited slot %d at pc %d has no parent upvalue"):format(i, pc), 2)
            end
        else
            error(("LumenV4: CAPTURE_VERIFY invalid capture kind %s at pc %d"):format(tostring(cap.kind), pc), 2)
        end
    end
    return true
end

function fn.caps(st, pc, child, closurekind)
    local out = {}
    local closureop = st.proto.Instructions[pc]
    local selfreg = closureop and closureop.A or nil
    local nx = st:next(pc)
    for i = 1, (child.UpvalueCount or 0) do
        local cp = nx
        local op = st.proto.Instructions[cp]
        local du = child.Upvalues and child.Upvalues[i]
        local dn = du and du.Name
        if not op or ins.name(op) ~= "CAPTURE" then
            error(("LumenV4: CAPTURE_VERIFY NEWCLOSURE at pc %d expected CAPTURE %d/%d"):format(pc, i, child.UpvalueCount or 0), 2)
        end

        local kind, src = op.A, op.B
        if closurekind == "dup" and kind == 1 then
            error(("LumenV4: CAPTURE_VERIFY DUPCLOSURE at pc %d cannot REF capture at pc %d"):format(pc, cp), 2)
        end
        if kind == 0 then
            out[i] = valuecap(st, cp, src, i, dn, selfreg)
        elseif kind == 1 then
            out[i] = refcap(st, cp, src, i, dn)
        elseif kind == 2 then
            out[i] = upcap(st, cp, src, i, dn)
        else
            error(("LumenV4: CAPTURE_VERIFY invalid CAPTURE mode %s at pc %d"):format(tostring(kind), cp), 2)
        end
        st.consumed[cp] = true
        nx = st:next(cp)
    end
    local extra = st.proto.Instructions[nx]
    if extra and ins.name(extra) == "CAPTURE" then
        error(("LumenV4: CAPTURE_VERIFY NEWCLOSURE at pc %d has more CAPTURE instructions than child upvalues"):format(pc), 2)
    end
    fn.verify(child, out, pc)
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
    caps = caps or {}
    local hint = child.Name
    if hint == nil or hint == "" then hint = st.ir.bestname and st.ir.bestname[st.ir:nameid(st:verdef(pc, r))] end
    if hint == nil or hint == "" then hint = "fn" .. tostring(r) end

    local target, assign, store = direct(st, pc, r, nx or st:next(pc))
    local value = st:verdef(pc, r)
    local symbol = value and st.ir:nameid(value) or ("r" .. tostring(r))
    local localname = st:defName(pc, r, hint)
    local selfcapture = false
    for _, cap in ipairs(caps) do
        if cap.kind == "self" then
            selfcapture = true
            cap.name = localname
        end
    end
    fn.verify(child, caps, pc)

    local root, sub, args = d:_child(child, caps, cbhints(st, pc, r))
    if not sub.v4 or sub.v4.captureVerified ~= true then
        error(("LumenV4: CAPTURE_VERIFY child at pc %d did not pass capture verification"):format(pc), 2)
    end
    st.v4.childCaptures = (st.v4.childCaptures or 0) + #caps

    if target and not selfcapture then
        st.consumed[store] = true
        if not assign and target:find("%.") and args[1] and (args[1]:match("^self%s*[:$]") or args[1] == "self") then
            local base, field = target:match("^(.*)%.([%a_][%w_]*)$")
            if base and field then target = base .. ":" .. field; table.remove(args, 1) end
        end
        st.ast:add({ kind = "function", name = target, args = table.concat(args, ", "), body = root, localfn = false, assign = assign })
    else
        local depth = st.declared[localname]
        local lexical = lit.identifier(localname)
        if lexical and (depth == nil or depth > st.indent) then
            st.declared[localname] = st.indent
            st:declaresymbol(symbol, localname, st.indent)
            st.ast:add({ kind = "function", name = localname, symbol = symbol, args = table.concat(args, ", "), body = root, localfn = true, assign = false })
        else
            if depth == nil or depth > st.indent then
                st.declared[localname] = st.indent
                st:declaresymbol(symbol, localname, st.indent)
            end
            st.ast:add({ kind = "function", name = localname, symbol = symbol, args = table.concat(args, ", "), body = root, localfn = false, assign = true })
        end
        if target then
            st.consumed[store] = true
            st:out(target .. " = " .. localname)
        end
    end
    for _, issue in ipairs(sub.bad) do st.bad[#st.bad + 1] = issue end
end

return fn
