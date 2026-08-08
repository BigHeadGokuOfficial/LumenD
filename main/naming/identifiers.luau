local id = {}

local kw = {
    ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true,
    ["end"] = true, ["false"] = true, ["for"] = true, ["function"] = true, ["if"] = true,
    ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true, ["or"] = true,
    ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
    ["until"] = true, ["while"] = true,
}

function id.valid(value)
    return type(value) == "string"
        and value:match("^[A-Za-z_][A-Za-z0-9_]*$")
        and not kw[value]
end

function id.clean(value)
    if type(value) ~= "string" then return nil end

    value = value:gsub("[^A-Za-z0-9_]", "_")
    value = value:gsub("_+", "_")
    value = value:gsub("^_+", "")
    value = value:gsub("_+$", "")

    if value == "" then return nil end
    if value:match("^[0-9]") then value = "_" .. value end
    if kw[value] then value = value .. "Value" end

    return value
end

function id.lowerCamel(value)
    value = id.clean(value)
    if not value then return nil end

    if value:match("^[A-Z][A-Z0-9_]+$") then
        value = value:lower()
    end

    return value:sub(1, 1):lower() .. value:sub(2)
end

return id