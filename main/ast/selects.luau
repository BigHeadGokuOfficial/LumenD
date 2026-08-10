local expr = require("main.output.expr")
local condition = require("main.ast.condition_utils")
local textutil = require("main.ast.text_utils")

local pass = {}

local function liveone(block)
    local found
    for _, node in ipairs(block.body or {}) do
        if not node.dead then
            if found then return nil end
            found = node
        end
    end
    return found
end

local function assignment(node)
    if not node then return nil end
    if node.kind == "assign" and not node.declare and #(node.names or {}) == 1 and #(node.values or {}) == 1 then
        local value = node.values[1]
        if type(value) == "table" and value.kind == "raw" and not textutil.singlevalue(expr.str(value)) then return nil end
        return node.names[1], value, node
    end
    if node.kind == "raw" and type(node.text) == "string" then
        local name, rhs = node.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
        if name and textutil.singlevalue(rhs) then return name, expr.raw(rhs, false), node end
    end
end

local function pick(node)
    if not node or node.kind ~= "if" or not node.elsebody or #(node.branches or {}) == 0 then return nil end

    local name
    local parts = {}
    for _, branch in ipairs(node.branches) do
        local n, value = assignment(liveone(branch.body))
        if not n or (name and n ~= name) then return nil end
        name = n
        parts[#parts + 1] = { cond = branch.cond, value = value }
    end

    local n, last = assignment(liveone(node.elsebody))
    if not n or n ~= name then return nil end

    if #parts == 1 then
        local a, b = expr.str(parts[1].value), expr.str(last)
        if a == b then return name, parts[1].value end
        if a == "true" and b == "false" then return name, expr.raw(parts[1].cond, false) end
        if a == "false" and b == "true" then return name, expr.raw(condition.negate(parts[1].cond), false) end
    end

    local out = "if " .. parts[1].cond .. " then " .. expr.str(parts[1].value)
    for i = 2, #parts do
        out = out .. " elseif " .. parts[i].cond .. " then " .. expr.str(parts[i].value)
    end
    out = out .. " else " .. expr.str(last)
    return name, expr.raw(out, false)
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
        local name, value = pick(node)
        if name then
            local previous = out[#out]
            if previous and previous.kind == "decl" and #(previous.names or {}) == 1 and previous.names[1] == name then
                out[#out] = {
                    kind = "assign",
                    names = { name },
                    symbols = previous.symbols,
                    annotations = previous.annotations,
                    values = { value },
                    declare = true,
                }
            else
                out[#out + 1] = {
                    kind = "assign",
                    names = { name },
                    values = { value },
                    declare = false,
                }
            end
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
