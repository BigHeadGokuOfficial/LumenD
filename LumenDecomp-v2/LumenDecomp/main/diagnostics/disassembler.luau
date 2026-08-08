local graph = require("main.analysis.graph")
local ins = require("main.bytecode.instructions")
local lit = require("main.output.literals")

local dis = {}

local function K(proto, index)
    return proto.Constants and proto.Constants[(index or 0) + 1]
end

local function opname(v)
    return v.OpCodeInfo and v.OpCodeInfo.Name or "?"
end

local function resolve(proto, v)
    local name = opname(v)
    local A, B, C, D = v.A, v.B, v.C, v.D
    local aux = v.AuxValue and v.AuxValue.Value or 0

    if name == "LOADK" then
        return "R" .. A .. " = " .. lit.constant(K(proto, D))
    elseif name == "LOADKX" then
        return "R" .. A .. " = " .. lit.constant(K(proto, aux))
    elseif name == "GETIMPORT" then
        return "R" .. A .. " = " .. lit.constant(K(proto, D))
    elseif name == "GETGLOBAL" then
        return "R" .. A .. " = " .. tostring(lit.rawStringConstant(K(proto, aux)))
    elseif name == "SETGLOBAL" then
        return tostring(lit.rawStringConstant(K(proto, aux))) .. " = R" .. A
    elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
        return "R" .. A .. " = " .. lit.property("R" .. B, lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff))))
    elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
        return lit.property("R" .. B, lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff)))) .. " = R" .. A
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        return "prepare R" .. A .. " = R" .. B .. ":" .. tostring(lit.rawStringConstant(K(proto, bit32.band(aux, 0xffff))))
    elseif ins.isConditional(v) or ins.isUnconditional(v) or name == "FORNPREP" then
        return "target=" .. tostring(ins.jumpTarget(v.Pc or 0, v))
    end
end

function dis.proto(proto)
    local cfg = graph.build(proto)
    local lines = {}

    for pc = 1, #proto.Instructions do
        if not cfg.aux[pc] then
            local op = proto.Instructions[pc]
            local info = op.OpCodeInfo or {}
            local suffix = resolve(proto, op)

            lines[#lines + 1] = string.format(
                "%04d  %-18s A=%-3s B=%-3s C=%-3s D=%-7s E=%-9s%s",
                pc,
                tostring(info.Name or "?"),
                tostring(op.A),
                tostring(op.B),
                tostring(op.C),
                tostring(op.D),
                tostring(op.E),
                suffix and (" ; " .. suffix) or ""
            )
        end
    end

    return table.concat(lines, "\n")
end

return dis
