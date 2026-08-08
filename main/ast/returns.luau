
local pass = {}

local function ret(b)
    if not b or #b.body ~= 1 then return nil end
    local n = b.body[1]
    if n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) then return nil end
    if v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function expr(n)
    if n.kind ~= "if" or not n.elsebody or #n.branches == 0 then return nil end
    local vals = {}
    for _, b in ipairs(n.branches) do
        local v = ret(b.body)
        if not v then return nil end
        vals[#vals + 1] = { cond = b.cond, val = v }
    end
    local last = ret(n.elsebody)
    if not last then return nil end
    if #vals == 1 then
        if vals[1].val == last then return vals[1].val end
        if vals[1].val == "true" and last == "false" then return vals[1].cond end
        if vals[1].val == "false" and last == "true" then return "not (" .. vals[1].cond .. ")" end
    end
    local out = "if " .. vals[1].cond .. " then " .. vals[1].val
    for i = 2, #vals do out = out .. " elseif " .. vals[i].cond .. " then " .. vals[i].val end
    return out .. " else " .. last
end

local function walk(b)
    for _, n in ipairs(b.body) do
        if n.kind == "if" then
            for _, x in ipairs(n.branches) do walk(x.body) end
            if n.elsebody then walk(n.elsebody) end
        elseif n.body then
            walk(n.body)
        end
    end
    local out = {}
    for _, n in ipairs(b.body) do
        local x = expr(n)
        if x then out[#out + 1] = { kind = "return", text = "return " .. x }
        else out[#out + 1] = n end
    end
    b.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
