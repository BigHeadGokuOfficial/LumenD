
local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function neg(s)
    s = trim(s)
    local x = s:match("^not%s+%((.+)%)$") or s:match("^not%s+(.+)$")
    if not x then return s end
    x = trim(x)
    local y = x:match("^not%s+%((.+)%)$") or x:match("^not%s+([%a_][%w_%.]*)$")
    if y then return trim(y) end
    for _, op in ipairs({ "~=", "==", "<=", ">=", "<", ">" }) do
        local a, b = x:match("^(.-)%s+" .. op:gsub("([^%w])", "%%%1") .. "%s+(.+)$")
        if a and b then return trim(a) .. " " .. inv[op] .. " " .. trim(b) end
    end
    return s
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do
                x.cond = neg(x.cond)
                walk(x.body)
            end
            if n.elsebody then walk(n.elsebody) end
        elseif n.kind == "while" or n.kind == "repeat" then
            n.cond = neg(n.cond)
            walk(n.body)
        elseif n.body then
            walk(n.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
