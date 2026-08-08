
local pass = {}

local function term(block)
    local body = block and block.body
    local last = body and body[#body]
    return last and (last.kind == "return" or last.kind == "break" or last.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.branches[1].body) then
                local rest = node.elsebody.body
                node.elsebody = nil
                out[#out + 1] = node
                for _, sub in ipairs(rest) do out[#out + 1] = sub end
            else
                out[#out + 1] = node
            end
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
