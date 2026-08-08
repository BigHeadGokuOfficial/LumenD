local pass = {}

local inv = {
    ["=="] = "~=", ["~="] = "==", ["<"] = ">=", ["<="] = ">",
    [">"] = "<=", [">="] = "<",
}

local cmp = { " ~= ", " == ", " <= ", " >= ", " < ", " > " }

local function neg(s)
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    for _, mid in ipairs(cmp) do
        local p = s:find(mid, 1, true)
        if p then
            local op = mid:sub(2, -2)
            local a = s:sub(1, p - 1)
            local b = s:sub(p + #mid)
            return a .. " " .. inv[op] .. " " .. b
        end
    end
    local x = s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
end

local function term(b)
    local x = b and b.body and b.body[#b.body]
    return x and (x.kind == "return" or x.kind == "break" or x.kind == "continue")
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, b in ipairs(node.branches) do walk(b.body) end
            if node.elsebody then walk(node.elsebody) end
            if #node.branches == 1 and node.elsebody and term(node.elsebody) and not term(node.branches[1].body) then
                out[#out + 1] = {
                    kind = "if",
                    branches = { { cond = neg(node.branches[1].cond), body = node.elsebody } },
                    elsebody = nil,
                }
                for _, x in ipairs(node.branches[1].body.body) do out[#out + 1] = x end
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
