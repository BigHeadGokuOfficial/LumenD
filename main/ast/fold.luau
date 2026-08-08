
local pass = {}

local function bool(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    if s == "true" then return true end
    if s == "false" or s == "nil" then return false end
    if s == "not true" then return false end
    if s == "not false" or s == "not nil" then return true end
    return nil
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            local keep = {}
            local done = false
            for _, b in ipairs(node.branches) do
                local v = bool(b.cond)
                if v == true then
                    if #keep == 0 then
                        for _, sub in ipairs(b.body.body) do out[#out + 1] = sub end
                    else
                        node.branches = keep
                        node.elsebody = b.body
                        out[#out + 1] = node
                    end
                    done = true
                    break
                elseif v == nil then
                    keep[#keep + 1] = b
                end
            end
            if not done then
                if #keep == 0 then
                    if node.elsebody then
                        for _, sub in ipairs(node.elsebody.body) do out[#out + 1] = sub end
                    end
                else
                    node.branches = keep
                    out[#out + 1] = node
                end
            end
        elseif node.kind == "while" then
            walk(node.body)
            if bool(node.cond) ~= false then out[#out + 1] = node end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
