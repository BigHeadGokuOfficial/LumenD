local expr = require("main.output.expr")

local pass = {}

local opmap = {
    ["//"] = "//=",
    [".."] = "..=",
    ["+"] = "+=",
    ["-"] = "-=",
    ["*"] = "*=",
    ["/"] = "/=",
    ["%"] = "%=",
    ["^"] = "^=",
}

local ordered = { "//", "..", "+", "-", "*", "/", "%", "^" }

local function semantic(node)
    if not node or node.kind ~= "assign" or node.declare or #(node.names or {}) ~= 1 or #(node.values or {}) ~= 1 then
        return nil
    end
    local name = node.names[1]
    local value = node.values[1]
    if type(value) ~= "table" or value.kind ~= "bin" or not opmap[value.op] then return nil end
    local lhs = value.a
    if type(lhs) ~= "table" or lhs.kind ~= "local" or lhs.value ~= name then return nil end
    return {
        kind = "raw",
        text = name .. " " .. opmap[value.op] .. " " .. expr.str(value.b),
    }
end

local function textual(node)
    if not node or node.kind ~= "raw" or type(node.text) ~= "string" then return nil end
    local name, rhs = node.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
    if not name then return nil end
    for _, op in ipairs(ordered) do
        local compound = opmap[op]
        local escaped = op:gsub("([^%w])", "%%%1")
        local tail = rhs:match("^" .. name .. "%s*" .. escaped .. "%s*(.+)$")
        if tail and tail ~= "" then
            return { kind = "raw", text = name .. " " .. compound .. " " .. tail }
        end
    end
end

local function walk(block)
    for i, node in ipairs(block.body or {}) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
        block.body[i] = semantic(node) or textual(node) or node
    end
end

function pass.run(root)
    walk(root)
    return root
end

return pass
