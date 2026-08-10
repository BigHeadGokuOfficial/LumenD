local condition = require("main.ast.condition_utils")
local textutil = require("main.ast.text_utils")

local pass = {}

local function onlyreturn(block)
    local node
    for _, item in ipairs(block and block.body or {}) do
        if not item.dead then
            if node then return nil end
            node = item
        end
    end
    if not node or node.kind ~= "return" or type(node.text) ~= "string" then return nil end
    local value = node.text:match("^return%s+(.+)$")
    if not value or value == "..." or not textutil.singlevalue(value) then return nil end
    return value
end

local function combine(cond, a, b)
    if a == b then return a end
    if a == "true" and b == "false" then return cond end
    if a == "false" and b == "true" then return condition.negate(cond) end
    return "if " .. cond .. " then " .. a .. " else " .. b
end

local function walk(block)
    for _, node in ipairs(block.body or {}) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #(block.body or {}) do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        if cur and cur.kind == "if" and #(cur.branches or {}) == 1 and not cur.elsebody and nxt and nxt.kind == "return" then
            local a = onlyreturn(cur.branches[1].body)
            local b = nxt.text and nxt.text:match("^return%s+(.+)$")
            if a and b and b ~= "..." and textutil.singlevalue(b) then
                out[#out + 1] = { kind = "return", text = "return " .. combine(cur.branches[1].cond, a, b) }
                i += 2
            else
                out[#out + 1] = cur
                i += 1
            end
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
