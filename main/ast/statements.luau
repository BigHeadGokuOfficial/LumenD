local expr = require("main.output.expr")

local pass = {}

local function splitnames(text)
    local names = {}
    for part in tostring(text or ""):gmatch("[^,]+") do
        local name = part:match("^%s*([%a_][%w_]*)%s*$")
        if not name then return nil end
        names[#names + 1] = name
    end
    return #names > 0 and names or nil
end

local function localstmt(text)
    local body = text:match("^local%s+(.+)$")
    if not body or body:match("^function%s") then return nil end

    local lhs, rhs = body:match("^(.-)%s*=%s*(.+)$")
    if lhs then
        local names = splitnames(lhs)
        if names then
            return {
                kind = "assign",
                names = names,
                values = { expr.raw(rhs, false) },
                declare = true,
            }
        end
        local name, ann = lhs:match("^%s*([%a_][%w_]*)%s*:%s*(.-)%s*$")
        if name and ann and ann ~= "" then
            return {
                kind = "assign",
                names = { name },
                annotations = { ann },
                values = { expr.raw(rhs, false) },
                declare = true,
            }
        end
        return nil
    end

    local names = splitnames(body)
    if names then return { kind = "decl", names = names } end

    local name, ann = body:match("^%s*([%a_][%w_]*)%s*:%s*(.-)%s*$")
    if name and ann and ann ~= "" then
        return { kind = "decl", names = { name }, annotations = { ann } }
    end
end

local function assignstmt(text)
    local lhs, rhs = text:match("^%s*(.-)%s*=%s*(.+)$")
    if not lhs or not rhs then return nil end
    local names = splitnames(lhs)
    if not names then return nil end
    return {
        kind = "assign",
        names = names,
        values = { expr.raw(rhs, false) },
        declare = false,
    }
end

local function convert(node)
    if not node or node.dead or node.kind ~= "raw" or type(node.text) ~= "string" then return node end
    return localstmt(node.text) or assignstmt(node.text) or node
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body or {}) do
        node = convert(node)
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end
        elseif node.body then
            walk(node.body)
        end
        out[#out + 1] = node
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
