local pass = {}

local list = {
    { "//", "//=" }, { "..", "..=" }, { "+", "+=" }, { "-", "-=" },
    { "*", "*=" }, { "/", "/=" }, { "%", "%=" }, { "^", "^=" },
}

local function pesc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function one(s)
    local name, rhs = s:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if not name then return s end
    local pre = "^" .. pesc(name) .. "%s*"
    for _, x in ipairs(list) do
        local tail = rhs:match(pre .. pesc(x[1]) .. "%s*(.+)$")
        if tail and tail ~= "" then return name .. " " .. x[2] .. " " .. tail end
    end
    return s
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "raw" then node.text = one(node.text)
        elseif node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
