local condition = require("main.ast.condition_utils")

local pass = {}

local function compactlive(block)
    local out = {}
    for _, node in ipairs(block.body or {}) do
        if node and not node.dead then out[#out + 1] = node end
    end
    block.body = out
end

local function exactnames(a, b)
    a, b = a or {}, b or {}
    if #a ~= #b then return false end
    for i = 1, #a do
        if a[i] ~= b[i] then return false end
    end
    return true
end

local function mergedecl(cur, nxt)
    local base = #(cur.names or {})
    cur.names = cur.names or {}
    cur.symbols = cur.symbols or {}
    cur.annotations = cur.annotations or {}
    for i, name in ipairs(nxt.names or {}) do
        cur.names[base + i] = name
        if nxt.symbols then cur.symbols[base + i] = nxt.symbols[i] end
        if nxt.annotations then cur.annotations[base + i] = nxt.annotations[i] end
    end
end

local function compactdecls(block)
    local body = block.body or {}
    local out = {}
    local i = 1
    while i <= #body do
        local cur = body[i]
        local nxt = body[i + 1]
        if cur and cur.kind == "decl" and nxt and nxt.kind == "assign"
            and not nxt.declare and exactnames(cur.names, nxt.names) then
            nxt.declare = true
            nxt.annotations = cur.annotations or nxt.annotations
            nxt.symbols = nxt.symbols or cur.symbols
            out[#out + 1] = nxt
            i += 2
        elseif cur and cur.kind == "decl" and nxt and nxt.kind == "decl" then
            mergedecl(cur, nxt)
            body[i + 1] = cur
            i += 1
        else
            out[#out + 1] = cur
            i += 1
        end
    end
    block.body = out
end

local function singlebreak(block)
    compactlive(block)
    return #block.body == 1 and block.body[1].kind == "break"
end

local function walk(block, opt)
    compactlive(block)

    for _, node in ipairs(block.body) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do walk(branch.body, opt) end
            if node.elsebody then walk(node.elsebody, opt) end

            while node.elsebody do
                compactlive(node.elsebody)
                if #node.elsebody.body ~= 1 then break end
                local sub = node.elsebody.body[1]
                if not sub or sub.kind ~= "if" then break end
                for _, branch in ipairs(sub.branches or {}) do
                    node.branches[#node.branches + 1] = branch
                end
                node.elsebody = sub.elsebody
            end

            if node.elsebody then
                compactlive(node.elsebody)
                if #node.elsebody.body == 0 then node.elsebody = nil end
            end

            if #node.branches == 1 and node.elsebody then
                local branch = node.branches[1]
                compactlive(branch.body)
                if #branch.body.body == 0 then
                    branch.cond = condition.negate(branch.cond)
                    branch.body = node.elsebody
                    node.elsebody = nil
                end
            end
        elseif node.kind == "while" then
            walk(node.body, opt)
            local truth = condition.strip(node.cond) == "true"
            local first = node.body.body[1]
            if truth and first and first.kind == "if" and #first.branches == 1
                and not first.elsebody and singlebreak(first.branches[1].body) then
                node.cond = condition.negate(first.branches[1].cond)
                table.remove(node.body.body, 1)
            end
        elseif node.body then
            walk(node.body, opt)
        end
    end

    compactlive(block)
    compactdecls(block)
    return block
end

function pass.run(root, opt)
    return walk(root, opt or {})
end

return pass
