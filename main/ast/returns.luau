local condition = require("main.ast.condition_utils")
local textutil = require("main.ast.text_utils")

local pass = {}

local function ret(block)
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

local function pick(node)
    if not node or node.kind ~= "if" or not node.elsebody or #(node.branches or {}) == 0 then return nil end
    local vals = {}
    for _, branch in ipairs(node.branches) do
        local value = ret(branch.body)
        if not value then return nil end
        vals[#vals + 1] = { cond = branch.cond, value = value }
    end
    local last = ret(node.elsebody)
    if not last then return nil end

    if #vals == 1 then
        local first = vals[1]
        if first.value == last then return first.value end
        if first.value == "true" and last == "false" then return first.cond end
        if first.value == "false" and last == "true" then return condition.negate(first.cond) end
    end

    local out = "if " .. vals[1].cond .. " then " .. vals[1].value
    for i = 2, #vals do
        out = out .. " elseif " .. vals[i].cond .. " then " .. vals[i].value
    end
    return out .. " else " .. last
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
    for _, node in ipairs(block.body or {}) do
        local value = pick(node)
        if value then
            out[#out + 1] = { kind = "return", text = "return " .. value }
        else
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
