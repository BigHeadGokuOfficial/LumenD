local pass = {}

local function exactnames(a, b)
    a, b = a or {}, b or {}
    if #a ~= #b then return false end
    for i = 1, #a do if a[i] ~= b[i] then return false end end
    return true
end

local function rawdecl(text)
    if type(text) ~= "string" then return nil end
    local name = text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.<>{}%[%]|&]+$")
        or text:match("^local%s+([%a_][%w_]*)$")
    return name
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
        local node = block.body[i]
        local nextn = block.body[i + 1]

        if node and node.kind == "decl" and nextn and nextn.kind == "assign"
            and not nextn.declare and exactnames(node.names, nextn.names) then
            nextn.declare = true
            nextn.annotations = node.annotations or nextn.annotations
            nextn.symbols = nextn.symbols or node.symbols
            out[#out + 1] = nextn
            i += 2
        elseif node and node.kind == "raw" and nextn and nextn.kind == "raw" then
            local name = rawdecl(node.text)
            local lhs, rhs = nextn.text and nextn.text:match("^([%a_][%w_]*)%s*=%s*(.+)$")
            if name and lhs == name then
                node.text = node.text .. " = " .. rhs
                out[#out + 1] = node
                i += 2
            else
                out[#out + 1] = node
                i += 1
            end
        else
            out[#out + 1] = node
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
