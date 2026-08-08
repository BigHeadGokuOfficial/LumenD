
local pass = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hits(s, name)
    local n = 0
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local at = 1
    while true do
        local a, b = s:find(pat, at)
        if not a then break end
        n += 1
        at = b + 1
    end
    return n
end

local function count(node, name)
    if not node or node.dead then return 0 end
    local n = 0
    if node.text then n += hits(node.text, name) end
    if node.cond then n += hits(node.cond, name) end
    if node.head then n += hits(node.head, name) end
    if node.args then n += hits(node.args, name) end
    if node.kind == "if" then
        for _, b in ipairs(node.branches) do
            n += hits(b.cond, name)
            for _, x in ipairs(b.body.body) do n += count(x, name) end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body) do n += count(x, name) end end
    elseif node.body then
        for _, x in ipairs(node.body.body) do n += count(x, name) end
    end
    return n
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
end

local function split(text, name)
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local a, b = text:find(pat)
    if not a then return nil end
    if text:find(pat, b + 1) then return nil end
    local pre = text:sub(1, a - 1)
    if not pre:find("%(") then return nil end
    return pre, text:sub(b + 1)
end

local function walk(block)
    for _, n in ipairs(block.body) do
        if n.kind == "if" then
            for _, b in ipairs(n.branches) do walk(b.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end

    local out = {}
    local i = 1
    while i <= #block.body do
        local cur = block.body[i]
        local nxt = block.body[i + 1]
        if cur and cur.kind == "function" and cur.localfn and nxt and nxt.kind == "raw"
            and count(cur, cur.name) == 0 and rest(block.body, i + 1, cur.name) == 1 then
            local pre, post = split(nxt.text, cur.name)
            if pre then
                out[#out + 1] = { kind = "callback", pre = pre, post = post, args = cur.args, body = cur.body }
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
