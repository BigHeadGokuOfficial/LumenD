
local id = require("main.naming.identifiers")

local lit = {}

function lit.identifier(value)
    return id.valid(value)
end

function lit.number(value)
    if value ~= value then return "(0 / 0)" end
    if value == math.huge then return "math.huge" end
    if value == -math.huge then return "-math.huge" end
    if value == 0 and 1 / value == -math.huge then return "-0.0" end
    return tostring(value)
end

function lit.string(value)
    return string.format("%q", value)
end

function lit.rawStringConstant(constant)
    if not constant then return nil end

    if constant.__type == "String" then
        local ok, result = pcall(buffer.tostring, constant.Value)
        if ok then return result end
    elseif constant.__type == "Import" then
        local parts = {}
        for _, item in ipairs(constant.Value) do
            local ok, result = pcall(buffer.tostring, item.Value)
            parts[#parts + 1] = ok and result or "?"
        end
        return table.concat(parts, ".")
    end

    return nil
end

local function tableKey(key)
    local raw = lit.rawStringConstant(key)
    if raw then
        if lit.identifier(raw) then
            return raw
        end
        return "[" .. lit.string(raw) .. "]"
    end

    return "[" .. lit.constant(key) .. "]"
end

function lit.constant(constant)
    if not constant then return "nil" end

    local kind = constant.__type

    if kind == "Nil" then
        return "nil"
    elseif kind == "Boolean" then
        return tostring(constant.Value)
    elseif kind == "Number" then
        return lit.number(constant.Value)
    elseif kind == "Integer" then
        local value = constant.Value
        if constant.IsNegative and type(value) == "number" and value > 0 then
            value = -value
        end
        return type(value) == "number" and lit.number(value) or tostring(value)
    elseif kind == "String" then
        return lit.string(lit.rawStringConstant(constant) or "")
    elseif kind == "Import" then
        return lit.rawStringConstant(constant) or "nil"
    elseif kind == "Vector" then
        return "Vector3.new(" .. lit.number(constant.X) .. ", " .. lit.number(constant.Y) .. ", " .. lit.number(constant.Z) .. ")"
    elseif kind == "Table" then
        return "{}"
    elseif kind == "TableWithConstants" then
        local parts = {}
        for _, pair in ipairs(constant.Value or {}) do
            local key = tableKey(pair.Key)
            local value = pair.Value and lit.constant(pair.Value) or "nil"
            parts[#parts + 1] = key .. " = " .. value
        end
        return "{ " .. table.concat(parts, ", ") .. " }"
    elseif kind == "Closure" then
        return "nil"
    elseif kind == "ClassShape" then
        return "nil"
    end

    return "nil"
end

function lit.property(base, field)
    if lit.identifier(field) then
        return base .. "." .. field
    end
    return base .. "[" .. lit.string(field or "?") .. "]"
end

return lit
