local pass = {}

local function asn(node)
    if not node or node.kind ~= "raw" then return nil end
    local a, b = node.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if a then return a, b end
end

local function decl(node)
    if not node or node.kind ~= "raw" then return nil end
    local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
    return name, name and node.text or nil
end

local function pick(node)
    if node.kind ~= "if" or not node.elsebody or #node.branches == 0 then return nil end
    local name
    local parts = {}
    for _, b in ipairs(node.branches) do
        if #b.body.body ~= 1 then return nil end
        local n, v = asn(b.body.body[1])
        if not n or (name and name ~= n) then return nil end
        name = n
        parts[#parts + 1] = { cond = b.cond, val = v }
    end
    if #node.elsebody.body ~= 1 then return nil end
    local n, v = asn(node.elsebody.body[1])
    if not n or n ~= name then return nil end
    if #parts == 1 then
        if parts[1].val == v then return name, v end
        if parts[1].val == "true" and v == "false" then return name, parts[1].cond end
        if parts[1].val == "false" and v == "true" then return name, "not (" .. parts[1].cond .. ")" end
    end
    local out = "if " .. parts[1].cond .. " then " .. parts[1].val
    for i = 2, #parts do out = out .. " elseif " .. parts[i].cond .. " then " .. parts[i].val end
    out = out .. " else " .. v
    return name, out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        local name, expr = pick(node)
        local prev = out[#out]
        local dn, dp = decl(prev)
        if name and dn == name then
            prev.text = dp .. " = " .. expr
        elseif name then
            out[#out + 1] = { kind = "raw", text = name .. " = " .. expr }
        else
            out[#out + 1] = node
        end
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass