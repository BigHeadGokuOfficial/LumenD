local condition = require("main.ast.condition_utils")

local pass = {}

local function walk(block)
    for _, node in ipairs(block.body or {}) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do
                branch.cond = condition.simplify(branch.cond)
                walk(branch.body)
            end
            if node.elsebody then walk(node.elsebody) end
        elseif node.kind == "while" or node.kind == "repeat" then
            node.cond = condition.simplify(node.cond)
            walk(node.body)
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
