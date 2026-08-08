local pass = {}

local function init(n)
    if not n or n.kind ~= "raw" then return nil end
    local a, b = n.text:match("^local%s+([%a_][%w_]*)%s*:%s*[%w_?%.]+%s*=%s*(.+)$")
    if a then return a, b end
    return n.text:match("^local%s+([%a_][%w_]*)%s*=%s*(.+)$")
end

local function simple(s)
    if s == "..." or s:find("%(") then return false end
    return true
end

local function word(s, name)
    local n = 0
    for x in s:gmatch("[%a_][%w_]*") do
        if x == name then n += 1 end
    end
    return n
end

local function count(n, name)
    if not n or n.dead then return 0 end
    local out = 0
    if n.text then out += word(n.text, name) end
    if n.cond then out += word(n.cond, name) end
    if n.head then out += word(n.head, name) end
    if n.args then out += word(n.args, name) end
    if n.kind == "if" then
        for _, b in ipairs(n.branches) do
            out += word(b.cond, name)
            for _, x in ipairs(b.body.body) do out += count(x, name) end
        end
        if n.elsebody then for _, x in ipairs(n.elsebody.body) do out += count(x, name) end end
    elseif n.body then
        for _, x in ipairs(n.body.body) do out += count(x, name) end
    end
    return out
end

local function rest(body, at, name)
    local n = 0
    for i = at, #body do n += count(body[i], name) end
    return n
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
        local name, rhs = init(cur)
        local used = name and rest(block.body, i + 1, name) or 0
        if name and nxt and used == 1 and simple(rhs) and nxt.kind == "return" and nxt.text == "return " .. name then
            out[#out + 1] = { kind = "return", text = "return " .. rhs }
            i += 2
        elseif name and nxt and used == 1 and simple(rhs) and nxt.kind == "if" and #nxt.branches > 0 then
            local c = nxt.branches[1].cond
            if c == name then
                nxt.branches[1].cond = rhs
                out[#out + 1] = nxt
                i += 2
            elseif c == "not " .. name or c == "not (" .. name .. ")" then
                nxt.branches[1].cond = "not (" .. rhs .. ")"
                out[#out + 1] = nxt
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
