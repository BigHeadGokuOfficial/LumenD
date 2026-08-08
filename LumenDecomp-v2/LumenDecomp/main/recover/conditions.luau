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
    st:set(fp, fo.A, x)
    return join
end

return cond
