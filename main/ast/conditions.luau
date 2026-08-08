local pass = {}

local function same(a, b)
    if a == b then return true end
    if type(a) ~= type(b) or type(a) ~= "table" then return false end
    for k, v in pairs(a) do
        if k ~= "dead" and not same(v, b[k]) then return false end
    end
    for k, v in pairs(b) do
        if k ~= "dead" and a[k] == nil and v ~= nil then return false end
    end
    return true
end

local function merge(node)
    local out = {}
    for _, b in ipairs(node.branches) do
        local prev = out[#out]
        if prev and same(prev.body, b.body) then
            prev.cond = "(" .. prev.cond .. ") or (" .. b.cond .. ")"
        else
            out[#out + 1] = b
        end
    end
    node.branches = out
end

local function walk(block)
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do
                walk(branch.body)
                local body = branch.body.body
                if #body == 1 and body[1].kind == "if" and not body[1].elsebody and #body[1].branches == 1 then
                    local sub = body[1]
                    branch.cond = "(" .. branch.cond .. ") and (" .. sub.branches[1].cond .. ")"
                    branch.body = sub.branches[1].body
                end
            end
            if node.elsebody then walk(node.elsebody) end
            merge(node)
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