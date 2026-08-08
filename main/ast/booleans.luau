
local pass = {}

local function val(n)
    if not n or n.kind ~= "return" then return nil end
    local v = n.text:match("^return%s+(.+)$")
    if not v or v:find(",", 1, true) or v == "..." or v:match("%)%s*$") then return nil end
    return v
end

local function neg(s)
    local x = s:match("^not%s+%((.*)%)$") or s:match("^not%s+(.+)$")
    if x then return x end
    return "not (" .. s .. ")"
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
        local done = false
        if cur and cur.kind == "if" and #cur.branches == 1 and not cur.elsebody and nxt and nxt.kind == "return" then
            local body = cur.branches[1].body
            if #body.body == 1 then
                local a = val(body.body[1])
                local b = val(nxt)
                if a and b then
                    local x
                    if a == "true" and b == "false" then x = cur.branches[1].cond
                    elseif a == "false" and b == "true" then x = neg(cur.branches[1].cond)
                    elseif a == b then x = a
                    else x = "if " .. cur.branches[1].cond .. " then " .. a .. " else " .. b end
                    out[#out + 1] = { kind = "return", text = "return " .. x }
                    i += 2
                    done = true
                end
            end
        end
        if not done then
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
