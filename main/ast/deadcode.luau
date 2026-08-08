local pass = {}

local function walk(block)
    local out = {}
    local done = false
    for _, node in ipairs(block.body) do
        if not node.dead and not done then
            if node.kind == "if" then
                for _, branch in ipairs(node.branches) do walk(branch.body) end
                if node.elsebody then walk(node.elsebody) end
            elseif node.body then
                walk(node.body)
            end
            out[#out + 1] = node
            if node.kind == "return" or node.kind == "break" or node.kind == "continue" then done = true end
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
