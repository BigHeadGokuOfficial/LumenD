
local pass = {}

local function walk(block)
    local out = {}
    local i = 1
    while i <= #block.body do
        local node = block.body[i]
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end

        local nextn = block.body[i + 1]
        if node.kind == "raw" and nextn and nextn.kind == "raw" then
            local name = node.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+$") or node.text:match("^local%s+([%a_][%w_]*)$")
            if name then
                local lhs, rhs = nextn.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
                if lhs == name then
                    node.text = node.text .. " = " .. rhs
                    i += 1
                end
            end
        end
        out[#out + 1] = node
        i += 1
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
