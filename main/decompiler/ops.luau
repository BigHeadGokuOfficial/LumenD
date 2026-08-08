
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")
local ex = require("main.output.expr")
local func = require("main.recover.functions")
local tab = require("main.recover.tables")

local ops = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kexpr(proto, i)
    return ex.atom(lit.constant(getk(proto, i)), true)
end

local function call(st, pc, op)
    local a, b, c = op.A, op.B, op.C
    local pending = st.namecall[a]
    local first = pending and a + 2 or a + 1
    local args = {}

    if b == 0 then
        if st.top and st.top.reg >= first then
            for r = first, st.top.reg - 1 do args[#args + 1] = st:use(pc, r) end
            args[#args + 1] = ex.str(st.top.node)
        end
    else
        for r = first, a + b - 1 do args[#args + 1] = st:use(pc, r) end
    end

    local node, hint
    if pending then
        local raw = st:raw(pc, a + 2)
        node = ex.call(ex.atom(pending.obj, false), args, pending.method)
        hint = st.naming.fromMethod(pending.method, raw)
        st.namecall[a] = nil
    else
        local callee = st:usex(pc, a)
        local raw = st:raw(pc, a + 1)
        node = ex.call(callee, args)
        hint = st.naming.fromCall(ex.str(callee), raw)
    end

    st.top = nil
    local rets = c == 0 and -1 or c - 1
    if rets == 0 then
        st:out(ex.str(node))
    elseif rets == -1 then
        st.top = { reg = a, node = node }
        local v = st:verdef(pc, a)
        if v then st.vals[v] = node end
    elseif rets == 1 then
        local v = st:verdef(pc, a)
        if v and st.ir:count(v) == 0 then st:out(ex.str(node)) else st:set(pc, a, node, hint) end
    else
        local regs, hints = {}, {}
        for r = a, a + rets - 1 do
            regs[#regs + 1] = r
            hints[#hints + 1] = r == a and hint or nil
        end
        st:multi(pc, regs, ex.str(node), hints, node)
    end
end

function ops.run(d, st, pc)
    if st.consumed[pc] or st.cfg.aux[pc] then return st:next(pc) end
    local op = st.proto.Instructions[pc]
    local name = ins.name(op)
    local a, b, c, dd = op.A, op.B, op.C, op.D
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" then
    elseif name == "LOADNIL" then st:set(pc, a, ex.atom("nil", true))
    elseif name == "LOADB" then
        st:set(pc, a, ex.atom(b == 1 and "true" or "false", true))
        if c ~= 0 then return pc + c + 1 end
    elseif name == "LOADN" then st:set(pc, a, ex.atom(tostring(dd), true))
    elseif name == "LOADK" then
        local k = getk(st.proto, dd)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "LOADKX" then
        local k = getk(st.proto, aux)
        local raw = k and k.__type == "String" and lit.rawStringConstant(k) or nil
        st:set(pc, a, ex.atom(lit.constant(k), true), nil, raw)
    elseif name == "MOVE" then
        st:set(pc, a, st:usex(pc, b), nil, st:raw(pc, b))
    elseif name == "GETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:set(pc, a, ex.atom(g, false), g)
    elseif name == "SETGLOBAL" then
        local g = lit.rawStringConstant(getk(st.proto, aux)) or "unknownGlobal"
        st:out(g .. " = " .. st:use(pc, a))
    elseif name == "GETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:set(pc, a, ex.atom(u, false), u)
    elseif name == "SETUPVAL" then
        local u = st.up[b + 1] or ("upvalue" .. tostring(b))
        st:out(u .. " = " .. st:use(pc, a))
    elseif name == "GETIMPORT" then
        local v = lit.rawStringConstant(getk(st.proto, dd)) or lit.constant(getk(st.proto, dd))
        st:set(pc, a, ex.atom(v, true), st.naming.fromImport(v))
    elseif name == "GETTABLE" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. st:use(pc, c) .. "]"))
    elseif name == "SETTABLE" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        local kv = st:veruse(pc, c)
        if t and not t.done and sv ~= tv and kv ~= tv then
            t.entries[#t.entries + 1] = { kind = "key", key = st:use(pc, c), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. st:use(pc, c) .. "] = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
        local ki = name == "GETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local suf = lit.identifier(f) and ("." .. f) or ("[" .. lit.string(f) .. "]")
        st:set(pc, a, ex.prop(st:usex(pc, b), suf), st.naming.fromField(f))
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
        local ki = name == "SETUDATAKS" and bit32.band(aux, 0xffff) or aux
        local f = lit.rawStringConstant(getk(st.proto, ki)) or "?"
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and lit.identifier(f) and sv ~= tv then
            tab.put(t, "field", f, st:usex(pc, a))
        else
            st:out(lit.property(st:use(pc, b), f) .. " = " .. st:use(pc, a))
        end
    elseif name == "GETTABLEN" then
        st:set(pc, a, ex.prop(st:usex(pc, b), "[" .. tostring(c + 1) .. "]"))
    elseif name == "SETTABLEN" then
        local tv = st:veruse(pc, b)
        local t = tv and st.tbl[tv]
        local sv = st:veruse(pc, a)
        if t and not t.done and sv ~= tv then
            local idx = c + 1
            local kind = idx == #t.entries + 1 and "list" or "key"
            t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = st:usex(pc, a) }
        else
            st:out(st:use(pc, b) .. "[" .. tostring(c + 1) .. "] = " .. st:use(pc, a))
        end
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        local ki = name == "NAMECALLUDATA" and bit32.band(aux, 0xffff) or aux
        st.namecall[a] = { obj = st:use(pc, b), method = lit.rawStringConstant(getk(st.proto, ki)) or "unknownMethod" }
    elseif name == "CALL" or name == "CALLFB" then
        call(st, pc, op)
    elseif name == "RETURN" then
        if b == 1 then
            st:out("return")
        elseif b == 0 and st.top and st.top.reg >= a then
            local vals = {}
            for r = a, st.top.reg - 1 do vals[#vals + 1] = st:use(pc, r) end
            vals[#vals + 1] = ex.str(st.top.node)
            st:out("return " .. table.concat(vals, ", "))
            st.top = nil
        elseif b == 0 then
            st:badpc(pc, "MULTRET return lost stack top")
            st:out("return " .. st:use(pc, a))
        else
            local vals = {}
            for r = a, a + b - 2 do vals[#vals + 1] = st:use(pc, r) end
            st:out("return " .. table.concat(vals, ", "))
        end
    elseif name == "NEWTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then st.tbl[v] = { reg = a, entries = {}, real = real, done = false }
        else st:set(pc, a, ex.atom("{}", false)) end
    elseif name == "DUPTABLE" then
        local v = st:verdef(pc, a)
        local safe = v ~= nil and not st.naming:isDebugAt(a, pc)
        local real = 0
        if safe then
            local block = st.cfg.blockmap[pc]
            for _, u in ipairs(st.ir:uses(v) or {}) do
                if not u.pc or st.cfg.blockmap[u.pc] ~= block then safe = false break end
                if not st:tblmut(u, a) then real += 1 end
            end
        end
        if safe then
            local entries, slots = tab.seed(getk(st.proto, dd))
            st.tbl[v] = { reg = a, entries = entries, slots = slots, real = real, done = false }
        else
            st:set(pc, a, ex.atom(lit.constant(getk(st.proto, dd)), false))
        end
    elseif name == "SETLIST" then
        local start = aux
        local tv = st:veruse(pc, a)
        local t = tv and st.tbl[tv]
        local vals = {}
        local mult = false
        if c == 0 then
            if st.top and st.top.reg >= b then
                for r = b, st.top.reg - 1 do vals[#vals + 1] = st:usex(pc, r) end
                vals[#vals + 1] = st.top.node
                mult = true
                st.top = nil
            else
                st:badpc(pc, "SETLIST MULTRET lost stack top")
            end
        else
            for i = 0, c - 2 do vals[#vals + 1] = st:usex(pc, b + i) end
        end
        local selfref = false
        for i = 1, #vals do
            local r = b + i - 1
            if st:veruse(pc, r) == tv then selfref = true break end
        end
        if t and not t.done and not selfref then
            for i, v in ipairs(vals) do
                local idx = start + i - 1
                local kind = idx == #t.entries + 1 and "list" or "key"
                t.entries[#t.entries + 1] = { kind = kind, key = tostring(idx), val = v }
            end
        elseif not mult then
            for i, v in ipairs(vals) do st:out(st:use(pc, a) .. "[" .. tostring(start + i - 1) .. "] = " .. ex.str(v)) end
        else
            local tmp = st.naming:unique("values")
            local args = {}
            for _, v in ipairs(vals) do args[#args + 1] = ex.str(v) end
            st:out("do")
            st.indent += 1
            st:out("local " .. tmp .. " = table.pack(" .. table.concat(args, ", ") .. ")")
            st:out("for i = 1, " .. tmp .. ".n do")
            st.indent += 1
            st:out(st:use(pc, a) .. "[" .. tostring(start) .. " + i - 1] = " .. tmp .. "[i]")
            st.indent -= 1
            st:out("end")
            st.indent -= 1
            st:out("end")
        end
    elseif name == "NEWCLOSURE" then
        local child = st.proto.Protos and st.proto.Protos[dd + 1]
        if child then local caps, nx = func.caps(st, pc, child); func.emit(d, st, pc, a, child, caps, nx)
        else st:badpc(pc, "missing NEWCLOSURE child proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "DUPCLOSURE" then
        local ck = getk(st.proto, dd)
        local child
        if d.parsed and ck and ck.__type == "Closure" then child = d.parsed.Protos[(ck.Value or 0) + 1] end
        if child then func.emit(d, st, pc, a, child, {}, st:next(pc))
        else st:badpc(pc, "missing DUPCLOSURE proto"); st:set(pc, a, ex.atom("function(...) end", false)) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        local map = { ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//", AND = "and", OR = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], st:usex(pc, c)))
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        local map = { ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//", ANDK = "and", ORK = "or" }
        st:set(pc, a, ex.bin(st:usex(pc, b), map[name], kexpr(st.proto, c)))
    elseif name == "SUBRK" or name == "DIVRK" then
        st:set(pc, a, ex.bin(kexpr(st.proto, b), name == "SUBRK" and "-" or "/", st:usex(pc, c)))
    elseif name == "CONCAT" then
        local vals = {}
        for r = b, c do vals[#vals + 1] = st:usex(pc, r) end
        st:set(pc, a, ex.join(vals, ".."))
    elseif name == "NOT" then st:set(pc, a, ex.un("not", st:usex(pc, b)))
    elseif name == "MINUS" then st:set(pc, a, ex.un("-", st:usex(pc, b)))
    elseif name == "LENGTH" then st:set(pc, a, ex.un("#", st:usex(pc, b)))
    elseif name == "GETVARARGS" then
        if b == 0 then
            st.top = { reg = a, node = ex.atom("...", false) }
            local v = st:verdef(pc, a)
            if v then st.vals[v] = st.top.node end
        elseif b == 2 then
            st:set(pc, a, ex.atom("...", false))
        else
            local regs = {}
            for r = a, a + b - 2 do regs[#regs + 1] = r end
            st:multi(pc, regs, "...")
        end
    elseif name == "CAPTURE" or name:match("^FASTCALL") then
    elseif name == "NEWCLASSMEMBER" then
        st:badpc(pc, "experimental NEWCLASSMEMBER approximated")
        local f = lit.rawStringConstant(getk(st.proto, aux)) or "member"
        st:out(lit.property(st:use(pc, a), f) .. " = " .. st:use(pc, c))
    elseif name == "NEWCLASS" then
        st:badpc(pc, "experimental NEWCLASS approximated")
        st:set(pc, a, ex.atom("{}", false))
    else
        st:badpc(pc, "unsupported opcode " .. tostring(name))
    end
    return st:next(pc)
end

return ops
