local irbuild = require("main.ir.build")
local irpass = require("main.passes.pipeline")
local names = require("main.naming.resolver")
local lower = require("main.ast.lower")
local astpass = require("main.ast.pipeline")
local printer = require("main.ast.printer")
local context = require("main.decompiler.context")
local ops = require("main.decompiler.ops")
local cond = require("main.recover.conditions")
local branch = require("main.recover.branches")
local loops = require("main.recover.loops")
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")
local regs = require("main.analysis.registers")
local vmfallback = (function()
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local vm = {}

local function line(out, depth, text)
    out[#out + 1] = string.rep("    ", depth) .. text
end

local function key2(proto, index)
    return proto.Constants and proto.Constants[(index or 0) + 1]
end

local function rawstr(constant)
    return lit.rawStringConstant(constant)
end

local function q(value)
    return lit.string(tostring(value or ""))
end

local function classshapeexpr(k)
    local name = rawstr(k and k.ClassName) or "AnonymousClass"
    local props, methods = {}, {}
    for _, v in ipairs(k and k.Properties or {}) do props[#props + 1] = q(rawstr(v) or "property") end
    for _, v in ipairs(k and k.Methods or {}) do methods[#methods + 1] = q(rawstr(v) or "method") end
    return "__classshape(" .. q(name) .. ", {" .. table.concat(props, ", ") .. "}, {" .. table.concat(methods, ", ") .. "})"
end

local function constexpr(proto, index)
    local k = key2(proto, index)
    if not k then return "nil" end
    if k.__type == "Import" then
        local parts = {}
        for _, part in ipairs(k.Value or {}) do parts[#parts + 1] = rawstr(part) or "?" end
        if #parts == 0 then return "nil" end
        local first = parts[1]
        local out
        if first == "type" and #parts == 1 then out = "__v4type"
        elseif first == "typeof" and #parts == 1 then out = "__v4typeof"
        elseif first == "class" then out = "__classlib"
        else out = "__env[" .. q(first) .. "]" end
        for i = 2, #parts do out = out .. "[" .. q(parts[i]) .. "]" end
        return out
    elseif k.__type == "ClassShape" then
        return classshapeexpr(k)
    elseif k.__type == "Closure" then
        return "nil"
    end
    return lit.constant(k)
end

local function aux(op)
    return op and op.AuxValue and op.AuxValue.Value or 0
end

local function methodkey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "unknownMethod"
end

local function tablekey(proto, op, userdata)
    local index = aux(op)
    if userdata then index = bit32.band(index, 0xffff) end
    return rawstr(key2(proto, index)) or "?"
end

local function realpcs(proto)
    local slots = ins.auxSlots(proto)
    local pcs = {}
    for pc = 1, #proto.Instructions do
        if not slots[pc] then pcs[#pcs + 1] = pc end
    end
    return pcs, slots
end

local function argsexpr(first, count, openlast)
    if openlast then
        return "__unpack(" .. tostring(first) .. ", __top - 1)"
    end
    local args = {}
    for i = 0, count - 1 do args[#args + 1] = "__get(" .. tostring(first + i) .. ")" end
    return table.concat(args, ", ")
end

local function emitcallresult(out, depth, ra, rc, callexpr)
    if rc == 1 then
        line(out, depth, callexpr)
        line(out, depth, "__top = nil")
        return
    end

    line(out, depth, "local __ret = table.pack(" .. callexpr .. ")")
    if rc == 0 then
        line(out, depth, "for __i = 1, __ret.n do __set(" .. tostring(ra) .. " + __i - 1, __ret[__i]) end")
        line(out, depth, "__top = " .. tostring(ra) .. " + __ret.n")
    else
        local n = rc - 1
        for i = 0, n - 1 do line(out, depth, "__set(" .. tostring(ra + i) .. ", __ret[" .. tostring(i + 1) .. "])") end
        line(out, depth, "__top = nil")
    end
end

local function captureinfo(proto, startpc, child, slots)
    local list = {}
    local pc = startpc
    for i = 1, (child and child.UpvalueCount or 0) do
        while slots[pc] do pc += 1 end
        local op = proto.Instructions[pc]
        if not op or ins.name(op) ~= "CAPTURE" then

            list[i] = { kind = 0, src = nil, malformed = true }
        else
            list[i] = { kind = op.A or 0, src = op.B or 0, pc = pc }
            pc = ins.next(proto, pc, slots)
        end
    end
    return list, pc
end

local function emitcapturearray(out, depth, captures, selfreg)
    local selfvals = {}
    line(out, depth, "local __caps = {}")
    line(out, depth, "local __modes = {}")
    line(out, depth, "local __selfcaps = {}")
    for i, c in ipairs(captures) do
        if c.malformed then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 0 and c.src == selfreg then

            selfvals[#selfvals + 1] = i
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = nil, ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
            line(out, depth, "__selfcaps[" .. tostring(i) .. "] = true")
        elseif c.kind == 0 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = {v = __get(" .. tostring(c.src) .. "), ref = false}")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 0")
        elseif c.kind == 1 then
            line(out, depth, "__caps[" .. tostring(i) .. "] = __cell(" .. tostring(c.src) .. ")")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 1")
        else
            local ui = tostring((c.src or 0) + 1)
            line(out, depth, "local __u" .. tostring(i) .. " = __up[" .. ui .. "]")
            line(out, depth, "if __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".ref then __caps[" .. tostring(i) .. "] = __u" .. tostring(i) .. " else __caps[" .. tostring(i) .. "] = {v = __u" .. tostring(i) .. " and __u" .. tostring(i) .. ".v or nil, ref = false} end")
            line(out, depth, "__modes[" .. tostring(i) .. "] = 2")
        end
    end
    return selfvals
end

local function protomap(parsed)
    local byobject = {}
    for i, p in ipairs(parsed.Protos or {}) do byobject[p] = i end
    return byobject
end

local function closurechild(parsed, proto, op, byobject)
    local name = ins.name(op)
    if name == "NEWCLOSURE" then
        local child = proto.Protos and proto.Protos[(op.D or 0) + 1]
        return child, child and byobject[child] or nil
    elseif name == "DUPCLOSURE" then
        local k = key2(proto, op.D)
        if k and k.__type == "Closure" then
            local id = (k.Value or 0) + 1
            return parsed.Protos and parsed.Protos[id], id
        end
    end
end

local function emitprotofactory(out, parsed, proto, id, byobject)
    local pcs, slots = realpcs(proto)
    local maxstack = math.max(1, tonumber(proto.MaxStackSize) or 255)
    local params = math.max(0, tonumber(proto.ParameterCount) or 0)
    local pnames = {}
    for i = 0, params - 1 do pnames[#pnames + 1] = "__a" .. tostring(i) end
    if proto.IsVararg then pnames[#pnames + 1] = "..." end

    line(out, 0, "__factory[" .. tostring(id) .. "] = function(__up)")
    line(out, 1, "local function __fn(" .. table.concat(pnames, ", ") .. ")")
    line(out, 2, "local __r, __open = {}, {}")
    line(out, 2, "local __top = nil")
    if proto.IsVararg then line(out, 2, "local __var = table.pack(...)") else line(out, 2, "local __var = {n = 0}") end
    for i = 0, params - 1 do line(out, 2, "__r[" .. tostring(i) .. "] = __a" .. tostring(i)) end

    line(out, 2, "local function __get(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then return __c.v end")
    line(out, 3, "return __r[__i]")
    line(out, 2, "end")
    line(out, 2, "local function __set(__i, __v)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c ~= nil then __c.v = __v else __r[__i] = __v end")
    line(out, 2, "end")
    line(out, 2, "local function __cell(__i)")
    line(out, 3, "local __c = __open[__i]")
    line(out, 3, "if __c == nil then __c = {v = __r[__i], ref = true}; __open[__i] = __c end")
    line(out, 3, "return __c")
    line(out, 2, "end")
    line(out, 2, "local function __close(__a)")
    line(out, 3, "for __i = __a, " .. tostring(maxstack - 1) .. " do")
    line(out, 4, "local __c = __open[__i]")
    line(out, 4, "if __c ~= nil then __r[__i] = __c.v; __open[__i] = nil end")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 2, "local function __unpack(__first, __last)")
    line(out, 3, "if __last == nil or __last < __first then return end")
    line(out, 3, "local __n = __last - __first + 1")
    line(out, 3, "local __a = {n = __n}")
    line(out, 3, "for __i = 1, __n do __a[__i] = __get(__first + __i - 1) end")
    line(out, 3, "return table.unpack(__a, 1, __n)")
    line(out, 2, "end")

    local firstpc = pcs[1] or 1
    line(out, 2, "local __pc = " .. tostring(firstpc))
    line(out, 2, "while true do")

    local consumedcaptures = {}
    for _, pc in ipairs(pcs) do
        local op = proto.Instructions[pc]
        local name = ins.name(op)
        if name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = closurechild(parsed, proto, op, byobject)
            if child then
                local captures = captureinfo(proto, ins.next(proto, pc, slots), child, slots)
                for _, c in ipairs(captures) do if c.pc then consumedcaptures[c.pc] = true end end
            end
        end
    end

    local branchindex = 0
    for _, pc in ipairs(pcs) do
        if not consumedcaptures[pc] then
            local op = proto.Instructions[pc]
            local name = ins.name(op)
            local nextpc = ins.next(proto, pc, slots)
            branchindex += 1
            line(out, 3, (branchindex == 1 and "if " or "elseif ") .. "__pc == " .. tostring(pc) .. " then")
            local d = 4
            local ra, rb2, rc, rd = op.A or 0, op.B or 0, op.C or 0, op.D or 0
            local av = aux(op)

            if name == "NOP" or name == "BREAK" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name:match("^FASTCALL") then
                line(out, d, "__pc = " .. tostring(nextpc))
            elseif name == "LOADNIL" then
                line(out, d, "__set(" .. ra .. ", nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADB" then
                line(out, d, "__set(" .. ra .. ", " .. (rb2 == 1 and "true" or "false") .. ")")
                line(out, d, "__pc = " .. tostring(rc ~= 0 and (pc + rc + 1) or nextpc))
            elseif name == "LOADN" then
                line(out, d, "__set(" .. ra .. ", " .. lit.number(rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LOADKX" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, av) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MOVE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                local value = key == "type" and "__v4type" or (key == "typeof" and "__v4typeof" or (key == "class" and "__classlib" or ("__env[" .. q(key) .. "]")))
                line(out, d, "__set(" .. ra .. ", " .. value .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETGLOBAL" then
                local key = rawstr(key2(proto, av)) or "unknownGlobal"
                line(out, d, "__env[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "__set(" .. ra .. ", __u and __u.v or nil)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETUPVAL" then
                line(out, d, "local __u = __up[" .. tostring(rb2 + 1) .. "]")
                line(out, d, "if __u == nil then __u = {v = nil, ref = true}; __up[" .. tostring(rb2 + 1) .. "] = __u end")
                line(out, d, "__u.v = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "CLOSEUPVALS" then
                line(out, d, "__close(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETIMPORT" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLE" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[__get(" .. rc .. ")])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLE" then
                line(out, d, "__get(" .. rb2 .. ")[__get(" .. rc .. ")] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
                local key = tablekey(proto, op, name == "GETUDATAKS")
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. q(key) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
                local key = tablekey(proto, op, name == "SETUDATAKS")
                line(out, d, "__get(" .. rb2 .. ")[" .. q(key) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "GETTABLEN" then
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "])"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETTABLEN" then
                line(out, d, "__get(" .. rb2 .. ")[" .. tostring(rc + 1) .. "] = __get(" .. ra .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWTABLE" then
                line(out, d, "__set(" .. ra .. ", {})"); line(out, d, "__pc = " .. nextpc)
            elseif name == "DUPTABLE" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rd) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
                local child, childid = closurechild(parsed, proto, op, byobject)
                local captures, after = captureinfo(proto, nextpc, child, slots)
                local selfvals = emitcapturearray(out, d, captures, ra)
                if childid then
                    if name == "DUPCLOSURE" then
                        line(out, d, "local __cl = __dup(" .. q(tostring(id) .. ":" .. tostring(rd)) .. ", " .. tostring(childid) .. ", __caps, __modes, __selfcaps)")
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    else
                        line(out, d, "local __cl = __factory[" .. tostring(childid) .. "](__caps)")
                        for _, ci in ipairs(selfvals) do line(out, d, "__caps[" .. tostring(ci) .. "].v = __cl") end
                        line(out, d, "__set(" .. ra .. ", __cl)")
                    end
                else
                    line(out, d, "__set(" .. ra .. ", function(...) return nil end)")
                end
                line(out, d, "__pc = " .. tostring(after))
            elseif name == "CAPTURE" then

                line(out, d, "__pc = " .. nextpc)
            elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
                local key = methodkey(proto, op, name == "NAMECALLUDATA")
                local callpc = nextpc
                local callop = proto.Instructions[callpc]
                local callname = callop and ins.name(callop) or ""
                if callop and (callname == "CALL" or callname == "CALLFB") and (callop.A or -1) == ra then
                    local cb, cc = callop.B or 0, callop.C or 0
                    local argtext
                    if cb == 0 then argtext = argsexpr(ra + 2, 0, true) else argtext = argsexpr(ra + 2, math.max(0, cb - 2), false) end
                    local callexpr
                    if lit.identifier(key) then
                        callexpr = "(__get(" .. rb2 .. ")):" .. key .. "(" .. argtext .. ")"
                    else
                        local pre = "(__get(" .. rb2 .. "))[" .. q(key) .. "]"
                        if argtext ~= "" then argtext = "__get(" .. rb2 .. "), " .. argtext else argtext = "__get(" .. rb2 .. ")" end
                        callexpr = "(" .. pre .. ")(" .. argtext .. ")"
                    end
                    emitcallresult(out, d, ra, cc, callexpr)
                    line(out, d, "__pc = " .. tostring(ins.next(proto, callpc, slots)))
                else
                    line(out, d, "local __obj = __get(" .. rb2 .. ")")
                    line(out, d, "__set(" .. ra .. ", __obj[" .. q(key) .. "])")
                    line(out, d, "__set(" .. tostring(ra + 1) .. ", __obj)")
                    line(out, d, "__pc = " .. nextpc)
                end
            elseif name == "CALL" or name == "CALLFB" then
                local argtext
                if rb2 == 0 then argtext = argsexpr(ra + 1, 0, true) else argtext = argsexpr(ra + 1, math.max(0, rb2 - 1), false) end
                emitcallresult(out, d, ra, rc, "(__get(" .. ra .. "))(" .. argtext .. ")")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "RETURN" then
                if rb2 == 1 then line(out, d, "return")
                elseif rb2 == 0 then line(out, d, "return __unpack(" .. ra .. ", (__top or " .. ra .. ") - 1)")
                else
                    local vals = {}
                    for r = ra, ra + rb2 - 2 do vals[#vals + 1] = "__get(" .. tostring(r) .. ")" end
                    line(out, d, "return " .. table.concat(vals, ", "))
                end
            elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "JUMPIF" or name == "JUMPIFNOT" then
                local test = name == "JUMPIF" and ("__get(" .. ra .. ")") or ("not __get(" .. ra .. ")")
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
                local rb = bit32.band(av, 0xff)
                local cmp = ({JUMPIFEQ = "==", JUMPIFNOTEQ = "~=", JUMPIFLT = "<", JUMPIFLE = "<=", JUMPIFNOTLT = "<", JUMPIFNOTLE = "<="})[name]
                local test = "__get(" .. ra .. ") " .. cmp .. " __get(" .. rb .. ")"
                if name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" then
                local rhs
                if name == "JUMPXEQKNIL" then rhs = "nil"
                elseif name == "JUMPXEQKB" then rhs = bit32.band(av, 1) == 1 and "true" or "false"
                else rhs = constexpr(proto, bit32.band(av, 0xffffff)) end
                local test = "__get(" .. ra .. ") == " .. rhs
                if bit32.btest(av, 0x80000000) then test = "not (" .. test .. ")" end
                line(out, d, "if " .. test .. " then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
                local symbol = ({ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " __get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" then
                local symbol = ({ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//"})[name]
                line(out, d, "__set(" .. ra .. ", __get(" .. rb2 .. ") " .. symbol .. " " .. constexpr(proto, rc) .. ")"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SUBRK" or name == "DIVRK" then
                line(out, d, "__set(" .. ra .. ", " .. constexpr(proto, rb2) .. (name == "SUBRK" and " - " or " / ") .. "__get(" .. rc .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "AND" or name == "OR" then
                if name == "AND" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rc .. ")) else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", __get(" .. rc .. ")) end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "ANDK" or name == "ORK" then
                local kval = constexpr(proto, rc)
                if name == "ANDK" then line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", " .. kval .. ") else __set(" .. ra .. ", __get(" .. rb2 .. ")) end")
                else line(out, d, "if __get(" .. rb2 .. ") then __set(" .. ra .. ", __get(" .. rb2 .. ")) else __set(" .. ra .. ", " .. kval .. ") end") end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CONCAT" then
                line(out, d, "local __x = __get(" .. rc .. ")")
                for r = rc - 1, rb2, -1 do line(out, d, "__x = __get(" .. r .. ") .. __x") end
                line(out, d, "__set(" .. ra .. ", __x)"); line(out, d, "__pc = " .. nextpc)
            elseif name == "NOT" then
                line(out, d, "__set(" .. ra .. ", not __get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "MINUS" then
                line(out, d, "__set(" .. ra .. ", -__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "LENGTH" then
                line(out, d, "__set(" .. ra .. ", #__get(" .. rb2 .. "))"); line(out, d, "__pc = " .. nextpc)
            elseif name == "SETLIST" then
                line(out, d, "local __t = __get(" .. ra .. ")")
                if rc == 0 then
                    line(out, d, "local __n = (__top or " .. rb2 .. ") - " .. rb2)
                    line(out, d, "for __i = 0, __n - 1 do __t[" .. av .. " + __i] = __get(" .. rb2 .. " + __i) end")
                    line(out, d, "__top = nil")
                else
                    for i = 0, rc - 2 do line(out, d, "__t[" .. tostring(av + i) .. "] = __get(" .. tostring(rb2 + i) .. ")") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "FORNPREP" then
                line(out, d, "local __limit = __fornum(__get(" .. ra .. "))")
                line(out, d, "local __step = __fornum(__get(" .. tostring(ra + 1) .. "))")
                line(out, d, "local __idx = __fornum(__get(" .. tostring(ra + 2) .. "))")
                line(out, d, "__set(" .. ra .. ", __limit); __set(" .. tostring(ra + 1) .. ", __step); __set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. nextpc .. " else __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " end")
            elseif name == "FORNLOOP" then
                line(out, d, "local __limit, __step = __get(" .. ra .. "), __get(" .. tostring(ra + 1) .. ")")
                line(out, d, "local __idx = __get(" .. tostring(ra + 2) .. ") + __step")
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __idx)")
                line(out, d, "if (__step > 0 and __idx <= __limit) or (not (__step > 0) and __limit <= __idx) then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then

                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGPREP" then
                line(out, d, "local __g = __get(" .. ra .. ")")
                line(out, d, "if type(__g) ~= \"function\" then")
                line(out, d + 1, "local __ng, __ns, __ni = __iterprep(__g)")
                line(out, d + 1, "__set(" .. ra .. ", __ng); __set(" .. tostring(ra + 1) .. ", __ns); __set(" .. tostring(ra + 2) .. ", __ni)")
                line(out, d, "end")
                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "FORGLOOP" then
                local count = math.max(1, bit32.band(av, 0xff))
                line(out, d, "local __ret = table.pack((__get(" .. ra .. "))(__get(" .. tostring(ra + 1) .. "), __get(" .. tostring(ra + 2) .. ")))")
                for i = 1, count do line(out, d, "__set(" .. tostring(ra + 2 + i) .. ", __ret[" .. tostring(i) .. "])") end
                line(out, d, "__set(" .. tostring(ra + 2) .. ", __ret[1])")
                line(out, d, "if __ret[1] ~= nil then __pc = " .. tostring(ins.jumpTarget(pc, op)) .. " else __pc = " .. nextpc .. " end")
            elseif name == "GETVARARGS" then
                if rb2 == 0 then
                    line(out, d, "for __i = 1, __var.n do __set(" .. ra .. " + __i - 1, __var[__i]) end")
                    line(out, d, "__top = " .. ra .. " + __var.n")
                else
                    for i = 1, rb2 - 1 do line(out, d, "__set(" .. tostring(ra + i - 1) .. ", __var[" .. tostring(i) .. "])") end
                end
                line(out, d, "__pc = " .. nextpc)
            elseif name == "CMPPROTO" then


                line(out, d, "__pc = " .. tostring(ins.jumpTarget(pc, op)))
            elseif name == "NEWCLASS" then
                line(out, d, "local __super = " .. (rb2 ~= 0xff and ("__get(" .. rb2 .. ")") or "nil"))
                line(out, d, "__set(" .. ra .. ", __newclass(" .. constexpr(proto, av) .. ", __super))")
                line(out, d, "__pc = " .. nextpc)
            elseif name == "NEWCLASSMEMBER" then
                local key = rawstr(key2(proto, av)) or "member"
                line(out, d, "__classmember(__get(" .. ra .. "), " .. q(key) .. ", __get(" .. rc .. "))")
                line(out, d, "__pc = " .. nextpc)
            else

                line(out, d, "error(" .. q("LumenV4 VM fallback: unknown opcode " .. tostring(name) .. " at pc " .. tostring(pc)) .. ")")
            end
        end
    end

    line(out, 3, "else")
    line(out, 4, "error(\"LumenV4 VM fallback: invalid pc \" .. tostring(__pc))")
    line(out, 3, "end")
    line(out, 2, "end")
    line(out, 1, "end")
    line(out, 1, "return __fn")
    line(out, 0, "end")
    line(out, 0, "")
end

function vm.run(parsed, reason)
    local entry = assert(parsed and parsed.Protos and parsed.Protos[parsed.ProtoEntryPoint], "LumenV4 VM fallback: missing entry proto")
    local byobject = protomap(parsed)
    local decoded = 0
    for _, proto in ipairs(parsed.Protos or {}) do
        local pcs = realpcs(proto)
        decoded += #pcs
    end
    local bytecodeversion = tonumber(parsed.BytecodeVersion) or 0
    local header = ("-- LumenV4 status=VM_FALLBACK coverage=100.00 reachable=%d covered=%d blocks=%d structuredBlocks=0 fallbackBlocks=%d phis=0 undefs=0 packs=0 cells=0 objects=0 escapedObjects=0 irreducible=0 bytecodeVersion=%d ssa=false parser=true diagnostics=0")
        :format(decoded, decoded, decoded, decoded, bytecodeversion)
    local out = {
        header,
        "-- Structured recovery failed; this function is a direct decoded-bytecode state machine.",
        "-- Original recovery reason: " .. tostring(reason or "semantic fallback"):gsub("[\r\n]+", " "),
        "local __env = (getfenv and getfenv(0)) or _G",
        "local __factory = {}",
        "local __dupcache = {}",
        "",
        "local function __fornum(v)",
        "    if type(v) == \"number\" then return v end",
        "    local n = tonumber(v)",
        "    if n == nil then error(\"invalid 'for' limit/step/index (number expected)\", 2) end",
        "    return n",
        "end",
        "",
        "local function __mt(v)",
        "    if type(getrawmetatable) == \"function\" then",
        "        local ok, mt = pcall(getrawmetatable, v)",
        "        if ok and mt ~= nil then return mt end",
        "    end",
        "    return getmetatable(v)",
        "end",
        "",
        "local function __iterprep(v)",
        "    if type(v) == \"table\" then",
        "        local mt = __mt(v)",
        "        local it = mt and mt.__iter",
        "        if it ~= nil then",
        "            local g, s, i = it(v)",
        "            return g, s, i",
        "        end",
        "        if mt and mt.__call then return v, nil, nil end",
        "        return next, v, nil",
        "    end",
        "    local mt = __mt(v)",
        "    local it = mt and mt.__iter",
        "    if it ~= nil then return it(v) end",
        "    return v, nil, nil",
        "end",
        "",
        "local __realtype = type",
        "local __realtypeof = typeof or type",
        "local __classof = setmetatable({}, {__mode = \"k\"})",
        "local __classmeta = setmetatable({}, {__mode = \"k\"})",
        "local __isclass = setmetatable({}, {__mode = \"k\"})",
        "",
        "local function __classshape(name, props, methods)",
        "    return {__name = name, __props = props, __methods = methods}",
        "end",
        "",
        "local function __classlookup(cls, key)",
        "    local c = cls",
        "    while c do",
        "        local v = rawget(c, key)",
        "        if v ~= nil then return v end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return nil",
        "end",
        "",
        "local function __isinstance(obj, cls)",
        "    if not __isclass[cls] then return false end",
        "    local c = __classof[obj]",
        "    while c do",
        "        if c == cls then return true end",
        "        local m = __classmeta[c]",
        "        c = m and m.super or nil",
        "    end",
        "    return false",
        "end",
        "",
        "local __classlib = setmetatable({",
        "    isinstance = __isinstance,",
        "    classof = function(v) return __classof[v] end,",
        "}, {__index = __env.class})",
        "",
        "local function __v4type(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtype(v)",
        "end",
        "local function __v4typeof(v)",
        "    if __isclass[v] then return \"class\" end",
        "    if __classof[v] then return \"object\" end",
        "    return __realtypeof(v)",
        "end",
        "",
        "local __classmetamethods = {",
        "    __add=true,__sub=true,__mul=true,__div=true,__idiv=true,__mod=true,__pow=true,",
        "    __unm=true,__len=true,__eq=true,__lt=true,__le=true,__concat=true,__tostring=true,",
        "    __iter=true,__call=true,",
        "}",
        "",
        "local function __classmember(cls, name, value)",
        "    rawset(cls, name, value)",
        "    local m = __classmeta[cls]",
        "    if m and __classmetamethods[name] then",
        "        m.instanceMt[name] = function(...) return value(...) end",
        "    end",
        "end",
        "",
        "local function __newclass(shape, super)",
        "    local cls = {}",
        "    local props, propset = {}, {}",
        "    if super and __classmeta[super] then",
        "        for _, p in ipairs(__classmeta[super].props) do props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    for _, p in ipairs(shape and shape.__props or {}) do",
        "        if not propset[p] then props[#props + 1] = p; propset[p] = true end",
        "    end",
        "    local imt = {}",
        "    local meta = {shape = shape or {}, super = super, props = props, propset = propset, instanceMt = imt}",
        "    __classmeta[cls] = meta",
        "    __isclass[cls] = true",
        "    imt.__index = function(obj, key)",
        "        local v = __classlookup(cls, key)",
        "        if v ~= nil then return v end",
        "        if propset[key] then return nil end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    imt.__newindex = function(obj, key, value)",
        "        if propset[key] then rawset(obj, key, value); return end",
        "        error(\"this object does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    local cmt = {}",
        "    cmt.__index = function(_, key)",
        "        local v = super and __classlookup(super, key) or nil",
        "        if v ~= nil then return v end",
        "        error(\"this class does not have a key named '\" .. tostring(key) .. \"'\", 2)",
        "    end",
        "    cmt.__newindex = function(_, key) error(\"attempt to index class with '\" .. tostring(key) .. \"'\", 2) end",
        "    cmt.__call = function(_, init)",
        "        local obj = {}",
        "        __classof[obj] = cls",
        "        setmetatable(obj, imt)",
        "        if init ~= nil then",
        "            for _, p in ipairs(props) do rawset(obj, p, init[p]) end",
        "        end",
        "        return obj",
        "    end",
        "    setmetatable(cls, cmt)",
        "    return cls",
        "end",
        "",
        "local function __samecaps(a, b, modes, selfcaps, fn)",
        "    if not a then return false end",
        "    for i = 1, #b do",
        "        if modes[i] == 0 then",
        "            local expected = selfcaps[i] and fn or (b[i] and b[i].v)",
        "            if not rawequal(a[i] and a[i].v, expected) then return false end",
        "        elseif modes[i] == 2 then",
        "            local ar, br = a[i] and a[i].ref, b[i] and b[i].ref",
        "            if ar or br then",
        "                if a[i] ~= b[i] then return false end",
        "            elseif not rawequal(a[i] and a[i].v, b[i] and b[i].v) then return false end",
        "        elseif a[i] ~= b[i] then return false end",
        "    end",
        "    return true",
        "end",
        "",
        "local function __dup(cacheKey, id, caps, modes, selfcaps)",
        "    local c = __dupcache[cacheKey]",
        "    if c ~= nil and __samecaps(c.caps, caps, modes, selfcaps, c.fn) then return c.fn end",
        "    local fn = __factory[id](caps)",
        "    for i in pairs(selfcaps) do caps[i].v = fn end",
        "    if c == nil then __dupcache[cacheKey] = {fn = fn, caps = caps, modes = modes} end",
        "    return fn",
        "end",
        "",
    }

    for i, proto in ipairs(parsed.Protos or {}) do emitprotofactory(out, parsed, proto, i, byobject) end
    local entryid = byobject[entry] or parsed.ProtoEntryPoint
    line(out, 0, "return (__factory[" .. tostring(entryid) .. "]({}))()")

    local source = table.concat(out, "\n")
    if type(loadstring) == "function" then
        local fn, err = loadstring(source, "@LumenV4/vm-fallback-verify")
        if not fn then error("LumenV4 VM fallback generator emitted invalid Luau: " .. tostring(err), 2) end
    end
    return source, {
        status = "VM_FALLBACK",
        fallback = true,
        syntaxValid = true,
        originCoverageValid = true,
        coverage = 1,
        verification = "decoded-bytecode-total-dispatch",
        structuredError = tostring(reason or ""),
    }
end

return vm
end)()

local decomp = {}
decomp.__index = decomp

local function loopused(st, r, a, b)
    local pc = a
    while pc < b do
        local uses = st.ssa.usesByPC[pc]
        if uses and uses[r] then return true end
        pc = st:next(pc)
    end
    return false
end

local function hashard(st)

    return #st.bad > 0
end

function decomp.new(opt) return setmetatable({ opt = opt or {} }, decomp) end

function decomp:_state(proto, up, ph)
    local ir = irbuild.run(proto)
    ir.paramhints = ph or {}
    ir = irpass.run(ir, self.opt)
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    local st = context.new(proto, ir, naming, up, lower.new(), self.opt)
    st.v4 = { fallback = false, visited = {}, status = "STRUCTURED", cellNames = {} }


    if ir.cells and next(ir.cells) then
        local oldvname = st.vname
        local ids = {}
        for cid in pairs(ir.cells) do ids[#ids + 1] = cid end
        table.sort(ids)
        local resolvedcell = {}
        for raw, cid in pairs(ir.cellOfValue or {}) do
            local rv = ir:resolve(raw)
            if rv then resolvedcell[rv] = resolvedcell[rv] or cid end
        end
        for _, cid in ipairs(ids) do
            local cell = ir.cells[cid]
            local cp = cell.captures and cell.captures[1]
            local raw = cp and ir.ssa.usesByPC[cp] and ir.ssa.usesByPC[cp][cell.reg] or nil
            if raw then
                st.v4.cellNames[cid] = oldvname(st, raw, cell.reg, nil, cp)
            else
                st.v4.cellNames[cid] = naming:unique("cell" .. tostring(cid))
            end
        end
        st.vname = function(self, value, reg, hint, pc)
            local cid = value and ((self.ir.cellOfValue and self.ir.cellOfValue[value]) or resolvedcell[self.ir:resolve(value)])
            local cellname = cid and self.v4.cellNames[cid]
            if cellname then return cellname end
            return oldvname(self, value, reg, hint, pc)
        end
    end


    for bid, phis in pairs(ir.phis or {}) do
        local block = assert(ir.cfg.blocks[bid], "LumenV4: phi references invalid CFG block")
        for reg, phi in pairs(phis) do
            local pid = ir:resolve(phi.id)
            if pid and not ir.dead[pid] then
                local target = st:vname(pid, reg, nil, block.startPC)
                for pred, raw in pairs(phi.incoming or {}) do
                    local rid = ir:resolve(raw)
                    local value = rid and ir.vals[rid] or nil
                    if value and value.kind ~= "undef" then
                        local pb = assert(ir.cfg.blocks[pred], "LumenV4: phi references invalid predecessor")
                        local source = st:vname(rid, reg, nil, pb.endPC)
                        if source ~= target then
                            error(("LumenV4: UNSUPPORTED SSA destruction mismatch for phi v%d r%d: b%d uses %s, target is %s")
                                :format(pid, reg, pred, tostring(source), tostring(target)), 2)
                        end
                    end
                end
            end
        end
    end
    st.v4.ssaDestructionVerified = true
    return st
end

local function arguments(st, proto)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    return args
end

local function preparepacks(st)
    st.packnames = {}
    st.directPacks = {}
    st.directPackValues = {}

    local consumers = {}
    for pc, producer in pairs(st.ssa.packInput or {}) do
        if type(producer) == "number" then
            local list = consumers[producer]
            if not list then list = {}; consumers[producer] = list end
            list[#list + 1] = pc
        end
    end

    local pcs = {}
    for pc, pack in pairs(st.ssa.packsByPC or {}) do
        if pack and pack.producesTop then pcs[#pcs + 1] = pc end
    end
    table.sort(pcs)

    local names = {}
    for _, pc in ipairs(pcs) do
        local list = consumers[pc] or {}
        local consumer = #list == 1 and list[1] or nil
        local sameblock = consumer and st.cfg.blockmap[pc] == st.cfg.blockmap[consumer]
        if consumer and sameblock and st:next(pc) == consumer then


            st.directPacks[pc] = consumer
        else
            local name = st.naming:unique("__pack" .. tostring(pc))
            st.packnames[pc] = name
            st.declared[name] = 0
            names[#names + 1] = name
        end
    end

    for i = 1, #names, 8 do
        local chunk = {}
        for j = i, math.min(i + 7, #names) do chunk[#chunk + 1] = names[j] end
        st:out("local " .. table.concat(chunk, ", "))
    end
end

local function packtail(st, pc)
    local producer = st.ssa.packInput and st.ssa.packInput[pc] or nil
    if producer == st.ssa.ambiguousPack then
        error("LumenV4: UNSUPPORTED divergent ValuePack at pc " .. tostring(pc), 2)
    end
    if type(producer) ~= "number" then
        error("LumenV4: UNSUPPORTED open ValuePack consumer without unique producer at pc " .. tostring(pc), 2)
    end
    local _, _, pp = regs.readWrite(st.proto.Instructions[producer])
    local direct = st.directPackValues and st.directPackValues[producer]
    if direct then return producer, pp.openWriteFrom, direct.node end
    local name = assert(st.packnames and st.packnames[producer], "LumenV4: missing ValuePack temp")
    return producer, pp.openWriteFrom, ex.atom("table.unpack(" .. name .. ", 1, " .. name .. ".n)", false)
end

function decomp:_op(st, pc)
    local op = st.proto.Instructions[pc]
    local _, _, pack = regs.readWrite(op)
    st.top = nil
    if pack.consumesTop then
        local _, base, node = packtail(st, pc)
        if type(base) ~= "number" then error("LumenV4: invalid ValuePack producer at pc " .. tostring(pc), 2) end
        if pack.openReadFrom and base < pack.openReadFrom then
            error("LumenV4: invalid ValuePack base at pc " .. tostring(pc), 2)
        end
        st.top = { reg = base, node = node, v4 = true }
    end

    local name = ins.name(op)
    local nx

    if name == "NEWTABLE" then
        st:set(pc, op.A, ex.atom("{}", false))
        nx = st:next(pc)
    elseif name == "DUPTABLE" then
        local constant = st.proto.Constants and st.proto.Constants[(op.D or 0) + 1]
        st:set(pc, op.A, ex.atom(lit.constant(constant), false))
        nx = st:next(pc)
    else
        nx = ops.run(self, st, pc)
    end

    if pack.producesTop then
        local produced = st.top
        if not produced or not produced.node then
            error("LumenV4: open-result producer did not expose a ValuePack at pc " .. tostring(pc), 2)
        end
        local base = assert(pack.openWriteFrom, "LumenV4: ValuePack producer has no base")
        if st.directPacks and st.directPacks[pc] then
            st.directPackValues[pc] = { reg = base, node = produced.node }
        else
            local name = assert(st.packnames and st.packnames[pc], "LumenV4: missing producer ValuePack temp")
            st:out(name .. " = table.pack(" .. ex.str(produced.node) .. ")")
            for reg, version in pairs(st.ssa.defsByPC[pc] or {}) do
                if reg >= base then
                    local node = ex.atom(name .. "[" .. tostring(reg - base + 1) .. "]", false)
                    st.vals[version] = node
                    st.expr[version] = node
                end
            end
        end
        st.top = nil
    end
    return nx
end

function decomp:_child(proto, up, ph)
    local st = self:_state(proto, up, ph)
    local args = arguments(st, proto)
    preparepacks(st)
    self:_region(st, 1, #proto.Instructions + 1, {})

    if hashard(st) then

        st = self:_state(proto, up, ph)
        args = arguments(st, proto)
        preparepacks(st)
        st.v4.fallback = true
        st.v4.status = "LOSSLESS_FALLBACK"
        self:_dispatcher(st)
        if hashard(st) then
            error("LumenV4: UNSUPPORTED semantic lowering issue: " .. table.concat(st.bad, " | "), 2)
        end
    end

    local root = astpass.run(st.ast:done(), self.opt)
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, a = info.loop, op.A


    local body = st:next(pc)
    local varreg = a + 2
    local bodystart = body
    local first = st.proto.Instructions[body]
    if first and ins.name(first) == "MOVE" and first.B == a + 2 and first.A == a + 3 then
        varreg = a + 3
        st.v4.visited[body] = true
        bodystart = st:next(body)
    end

    local old = st.alias[varreg]
    local lv = varreg == a + 2 and st:veruse(body, varreg) or st:verdef(body, varreg)
    if not lv then lv = st:veruse(loop, a + 2) or st:verdef(loop, a + 2) end
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, varreg, bodystart, loop) and "_" or st:vname(lv, varreg, fall, body)
    local limit, step, init = ex.str(st:loopx(pc, loop, a)), ex.str(st:loopx(pc, loop, a + 1)), ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head ..= ", " .. step end
    st:out(head .. " do"); st.indent += 1
    st.alias[varreg] = var; st.declared[var] = st.indent
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, bodystart, loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end"); st.alias[varreg] = old
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop, lop = info.loop, info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth, vars, old = (active.loopdepth or 0) + 1, {}, {}
    for i = 1, n do
        local r = op.A + 2 + i; old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end
    local src
    local rs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A); local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, rs) then src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2)) end
    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do"); st.indent += 1
    for i = 1, n do local r = op.A + 2 + i; st.alias[r] = vars[i]; st.declared[vars[i]] = st.indent end
    local prev, olddepth = active.loop, active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }; active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop, active.loopdepth = prev, olddepth
    st:trim(st.indent); st.indent -= 1; st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    st.v4.visited[loop] = true
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then"); st.indent += 1
    local old = active.join; active.join = info.join
    self:_region(st, info.a, info.b, active); active.join = old
    st:trim(st.indent); st.indent -= 1
    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then self:_emitif(st, sub, active, "elseif"); return end
        st:out("else"); st.indent += 1; old = active.join; active.join = info.join
        self:_region(st, info.c, info.d, active); active.join = old
        st:trim(st.indent); st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start; active = active or {}
    while pc < stop and pc <= #st.proto.Instructions do
        if st.cfg.aux[pc] then pc += 1
        elseif st.consumed[pc] then st.v4.visited[pc] = true; pc += 1
        else
            st.v4.visited[pc] = true
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then


                st:hoist(pc)
                active["repeat:" .. tostring(pc)] = true; st:out("repeat"); st.indent += 1
                local prev = active.loop; active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active); active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch]); st.v4.visited[rep.latch] = true
                st:trim(st.indent); st.indent -= 1; st:out("until " .. ex.str(x)); active["repeat:" .. tostring(pc)] = nil; pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then

                    st:hoist(pc)
                    st:out("while true do"); st.indent += 1; local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active); active.loop = prev; st.v4.visited[forever.latch] = true
                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]; local name = ins.name(op)
                    if name == "FORNPREP" then pc = self:_numfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then pc = self:_genfor(st, pc, op, stop, active) or self:_op(st, pc)
                    elseif name == "CMPPROTO" then
                        local target, join = ins.jumpTarget(pc, op), st:join(pc)
                        if join and target > pc and target < join and join <= stop then self:_region(st, target, join, active); pc = join
                        else st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target)); pc = st:next(pc) end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop, target = active.loop, ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end"); pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc); st:out("while " .. ex.str(wh.cond) .. " do"); st.indent += 1
                                    local prev = active.loop; active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active); active.loop = prev
                                    st:trim(st.indent); st.indent -= 1; st:out("end"); pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then st:hoist(info.join); self:_emitif(st, info, active); pc = info.join
                                    else st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target)); pc = st:next(pc) end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target, loop = ins.jumpTarget(pc, op), active.loop
                        if loop and target == loop.breakpc then st:out("break"); pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then st:out("continue"); pc = st:next(pc)
                        elseif target == stop or target == active.join then pc = stop
                        else st:badpc(pc, "unstructured jump -> " .. tostring(target)); pc = st:next(pc) end
                    else pc = self:_op(st, pc) end
                end
            end
        end
    end
    return pc
end

local function dispatcherunsupported(st)
    for _, n in ipairs(st.ir.ops) do
        local name = n.name
        if name == "FORNPREP" or name == "FORNLOOP" or name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" or name == "FORGLOOP" then
            return "dispatcher requires VM loop-state emulation for " .. name .. " at pc " .. tostring(n.pc)
        end
        if name == "CMPPROTO" then return "CMPPROTO cannot be represented losslessly in source fallback at pc " .. tostring(n.pc) end
        if name == "CLOSEUPVALS" then return "dispatcher would change upvalue close/cell lifetime at pc " .. tostring(n.pc) end
        if name == "CAPTURE" and n.op.A == 1 then return "dispatcher would hoist a by-reference captured local cell at pc " .. tostring(n.pc) end
    end
end

function decomp:_dispatcher(st)
    local why = dispatcherunsupported(st)
    if why then error("LumenV4: UNSUPPORTED lossless fallback: " .. why, 2) end


    local nameset, ordered = {}, {}
    for id, v in ipairs(st.ir.vals) do
        if v and not st.ir.dead[id] and v.kind ~= "param" and v.kind ~= "undef" then
            local name = st:vname(id, v.reg, nil, v.pc or 1)
            if name and not nameset[name] and st.declared[name] == nil then nameset[name] = true; ordered[#ordered + 1] = name end
        end
    end
    table.sort(ordered)
    for i = 1, #ordered, 12 do
        local chunk = {}; for j = i, math.min(i + 11, #ordered) do chunk[#chunk + 1] = ordered[j]; st.declared[ordered[j]] = 0 end
        st:out("local " .. table.concat(chunk, ", "))
    end

    local state = st.naming:unique("__lumenstate")
    st.declared[state] = 0
    st:out("local " .. state .. " = 1")
    st:out("while true do"); st.indent += 1

    for bi, b in ipairs(st.cfg.blocks) do
        st:out((bi == 1 and "if " or "elseif ") .. state .. " == " .. tostring(b.id) .. " then")
        st.indent += 1
        st.top = nil
        for pi, pc in ipairs(b.pcs) do
            st.v4.visited[pc] = true
            if not st.consumed[pc] then
                local op, name = st.proto.Instructions[pc], ins.name(st.proto.Instructions[pc])
                local last = pi == #b.pcs
                if last and ins.isConditional(op) then
                    local target, fall = st.cfg.blockmap[ins.jumpTarget(pc, op)], st.cfg.blockmap[st:next(pc)]
                    if not target or not fall then error("LumenV4: invalid dispatcher conditional edge at pc " .. tostring(pc), 2) end
                    st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then")
                    st.indent += 1; st:out(state .. " = " .. tostring(target)); st.indent -= 1
                    st:out("else"); st.indent += 1; st:out(state .. " = " .. tostring(fall)); st.indent -= 1; st:out("end")
                elseif last and (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") then
                    local target = st.cfg.blockmap[ins.jumpTarget(pc, op)]
                    if not target then error("LumenV4: invalid dispatcher jump edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                elseif last and name == "LOADB" and (op.C or 0) ~= 0 then
                    self:_op(st, pc)
                    local target = st.cfg.blockmap[pc + op.C + 1]
                    if not target then error("LumenV4: invalid LOADB edge at pc " .. tostring(pc), 2) end
                    st:out(state .. " = " .. tostring(target))
                else
                    self:_op(st, pc)
                    if last and name ~= "RETURN" then
                        if #b.successors == 1 then st:out(state .. " = " .. tostring(b.successors[1]))
                        elseif #b.successors == 0 then st:out("break")
                        elseif #b.successors > 1 then error("LumenV4: unhandled multi-successor block at pc " .. tostring(pc), 2) end
                    end
                end
            end
        end
        st.indent -= 1
    end
    st:out("else"); st.indent += 1; st:out("error(\"LumenV4: invalid dispatcher state \" .. tostring(" .. state .. "))"); st.indent -= 1
    st:out("end")
    st.indent -= 1; st:out("end")
end

local function metrics(st)
    local reachable, covered = 0, 0
    for pc = 1, #st.proto.Instructions do
        if not st.cfg.aux[pc] and st.cfg.blockmap[pc] then
            reachable += 1
            if st.v4.visited[pc] or st.consumed[pc] then covered += 1 end
        end
    end
    return reachable, covered, reachable == 0 and 1 or covered / reachable
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    local src = printer.run(root, self.opt)
    local reachable, covered, coverage = metrics(st)
    if covered ~= reachable then
        error(("LumenV4: PARTIAL origin coverage %d/%d (%.2f%%)"):format(covered, reachable, coverage * 100), 2)
    end
    local ss = st.ssa:summary()
    local structuredblocks = st.v4.fallback and 0 or #st.cfg.blocks
    local fallbackblocks = st.v4.fallback and #st.cfg.blocks or 0
    local objectcount, escapedobjects = 0, 0
    for _, obj in pairs(st.ir.objects or {}) do
        objectcount += 1
        if obj.escaped then escapedobjects += 1 end
    end
    local cellcount = 0
    for _ in pairs(st.ir.cells or {}) do cellcount += 1 end
    local packcount = 0
    for _, pack in pairs(st.ssa.packsByPC or {}) do if pack and pack.producesTop then packcount += 1 end end
    local irreducible = st.cfg.irreducible and 1 or 0
    local bytecodeversion = self.parsed and self.parsed.BytecodeVersion or 0

    if type(loadstring) ~= "function" then
        error("LumenV4: UNSUPPORTED syntax verification requires loadstring()", 2)
    end

    local header = ("-- LumenV4 status=%s coverage=%.2f reachable=%d covered=%d blocks=%d structuredBlocks=%d fallbackBlocks=%d phis=%d undefs=%d packs=%d cells=%d objects=%d escapedObjects=%d irreducible=%d bytecodeVersion=%d ssa=true parser=true diagnostics=%d\n")
        :format(st.v4.status, coverage * 100, reachable, covered, #st.cfg.blocks, structuredblocks, fallbackblocks,
            ss.phis or 0, ss.undefs or 0, packcount, cellcount, objectcount, escapedobjects, irreducible, bytecodeversion, #st.bad)
    src = header .. src
    local check, err = loadstring(src, "@LumenV4/verify")
    if not check then error("LumenV4: INVALID emitted Luau: " .. tostring(err), 2) end

    return src, {
        status = st.v4.status, cfg = st.cfg, ir = st.ir, ssa = st.ssa, ssaSummary = ss, issues = st.bad,
        coverage = coverage, coveredInstructions = covered, reachableInstructions = reachable, fallback = st.v4.fallback,
        syntaxValid = true, originCoverageValid = true, verification = "syntax+CFG-origin-invariants",
        objectCount = objectcount, escapedObjects = escapedobjects, cellCount = cellcount, valuePackCount = packcount,
        irreducible = st.cfg.irreducible == true, bytecodeVersion = bytecodeversion,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenV4: parsed bytecode has no entry proto")
    self.parsed = parsed

    local ok, src, info = pcall(function() return self:decompileProto(proto, {}) end)
    if ok then
        self.parsed = nil
        return src, info
    end


    local structurederror = tostring(src)
    local fok, fsrc, finfo = pcall(function()
        return vmfallback.run(parsed, structurederror)
    end)
    self.parsed = nil

    if not fok then
        error("LumenV4: VM fallback generator failure after structured failure: " .. tostring(fsrc)
            .. " | structured: " .. structurederror, 2)
    end
    return fsrc, finfo
end

return decomp
