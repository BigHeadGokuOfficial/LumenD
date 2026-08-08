local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local pass = {}

local function getk(proto, i)
    return proto.Constants and proto.Constants[(i or 0) + 1]
end

local function kval(k)
    if not k then return nil, true end
    local t = k.__type
    if t == "Nil" then return nil, true end
    if t == "Boolean" or t == "Number" then return k.Value, true end
    if t == "Integer" then
        local v = k.Value
        if k.IsNegative and type(v) == "number" and v > 0 then v = -v end
        return v, true
    end
    if t == "String" then return lit.rawStringConstant(k), true end
    return nil, false
end

local function text(v)
    local t = type(v)
    if v == nil then return "nil" end
    if t == "string" then return lit.string(v) end
    if t == "boolean" or t == "number" then return tostring(v) end
    return nil
end

local function truth(v)
    return v ~= nil and v ~= false
end

local function calc(op, a, b)
    local ok, out = pcall(function()
        if op == "ADD" or op == "ADDK" then return a + b end
        if op == "SUB" or op == "SUBK" then return a - b end
        if op == "MUL" or op == "MULK" then return a * b end
        if op == "DIV" or op == "DIVK" then return a / b end
        if op == "MOD" or op == "MODK" then return a % b end
        if op == "POW" or op == "POWK" then return a ^ b end
        if op == "IDIV" or op == "IDIVK" then return math.floor(a / b) end
        if op == "SUBRK" then return a - b end
        if op == "DIVRK" then return a / b end
        if op == "AND" or op == "ANDK" then return truth(a) and b or a end
        if op == "OR" or op == "ORK" then return truth(a) and a or b end
    end)
    return ok and out or nil, ok
end

function pass.run(ir)
    ir.constval = {}

    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local defs = ir.ssa.defsByPC[n.pc]
        local id = defs and defs[op.A] and ir:resolve(defs[op.A]) or nil
        local v, known = nil, false

        if name == "LOADNIL" then v, known = nil, true
        elseif name == "LOADB" then v, known = op.B == 1, true
        elseif name == "LOADN" then v, known = op.D, true
        elseif name == "LOADK" then v, known = kval(getk(ir.proto, op.D))
        elseif name == "LOADKX" then v, known = kval(getk(ir.proto, op.AuxValue and op.AuxValue.Value or 0))
        elseif name == "MOVE" then
            local src = ir:use(n.pc, op.B)
            if src and ir.constval[src] ~= nil then v, known = ir.constval[src].v, true
            elseif src and ir.constval[src] and ir.constval[src].nilv then v, known = nil, true end
        elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
            local src = ir:use(n.pc, op.B)
            local cv = src and ir.constval[src]
            if cv then
                local a = cv.nilv and nil or cv.v
                if name == "NOT" then v, known = not truth(a), true
                elseif name == "MINUS" and type(a) == "number" then v, known = -a, true
                elseif name == "LENGTH" and type(a) == "string" then v, known = #a, true end
            end
        else
            local rr = {
                ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true, IDIV = true,
                AND = true, OR = true,
            }
            local rk = {
                ADDK = true, SUBK = true, MULK = true, DIVK = true, MODK = true, POWK = true, IDIVK = true,
                ANDK = true, ORK = true,
            }
            if rr[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if av and bv then
                    v, known = calc(name, av.nilv and nil or av.v, bv.nilv and nil or bv.v)
                end
            elseif rk[name] then
                local av = ir.constval[ir:use(n.pc, op.B)]
                local b, bk = kval(getk(ir.proto, op.C))
                if av and bk then v, known = calc(name, av.nilv and nil or av.v, b) end
            elseif name == "SUBRK" or name == "DIVRK" then
                local a, ak = kval(getk(ir.proto, op.B))
                local bv = ir.constval[ir:use(n.pc, op.C)]
                if ak and bv then v, known = calc(name, a, bv.nilv and nil or bv.v) end
            end
        end

        if id and known then
            ir.constval[id] = v == nil and { nilv = true } or { v = v }
            local s = text(v)
            if s then ir.const[id] = s end
        end
    end
    return ir
end

return pass
