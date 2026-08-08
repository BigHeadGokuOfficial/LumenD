local pass = {}

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
