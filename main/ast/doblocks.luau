local pass = {}

local function words(s, out)
    if type(s) ~= "string" then return end
    for x in s:gmatch("[%a_][%w_]*") do out[x] = true end
end

local function declraw(s)
    if type(s) ~= "string" then return {} end
    local head = s:match("^local%s+(.+)$")
    if not head or head:match("^function%s") then return {} end
    head = head:match("^(.-)%s*=") or head
    local out = {}
    for part in head:gmatch("[^,]+") do
        local name = part:match("^%s*([%a_][%w_]*)")
        if name then out[#out + 1] = name end
    end
    return out
end

local function decls(n)
    if n.kind == "raw" then return declraw(n.text) end
    if n.kind == "function" and n.localfn then return { n.name } end
    return {}
end

local function scanblock(b, out)
    for _, n in ipairs(b.body or {}) do
        if not n.dead then
            if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
                words(n.text, out)
            elseif n.kind == "if" then
                for _, x in ipairs(n.branches or {}) do
                    words(x.cond, out)
                    scanblock(x.body, out)
                end
                if n.elsebody then scanblock(n.elsebody, out) end
            elseif n.kind == "while" or n.kind == "repeat" then
                words(n.cond, out)
                scanblock(n.body, out)
            elseif n.kind == "for" then
                words(n.head, out)
                scanblock(n.body, out)
            elseif n.kind == "do" then
                scanblock(n.body, out)
            elseif n.kind == "callback" then
                words(n.pre, out)
                words(n.args, out)
                words(n.post, out)
                scanblock(n.body, out)
            elseif n.kind == "function" then
                words(n.name, out)
                words(n.args, out)
                scanblock(n.body, out)
            end
        end
    end
end

local function refs(n)
    local out = {}
    if n.kind == "raw" or n.kind == "return" or n.kind == "break" or n.kind == "continue" then
        words(n.text, out)
    elseif n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do
            words(x.cond, out)
            scanblock(x.body, out)
        end
        if n.elsebody then scanblock(n.elsebody, out) end
    elseif n.kind == "while" or n.kind == "repeat" then
        words(n.cond, out)
        scanblock(n.body, out)
    elseif n.kind == "for" then
        words(n.head, out)
        scanblock(n.body, out)
    elseif n.kind == "do" then
        scanblock(n.body, out)
    elseif n.kind == "callback" then
        words(n.pre, out)
        words(n.args, out)
        words(n.post, out)
        scanblock(n.body, out)
    elseif n.kind == "function" then
        words(n.name, out)
        words(n.args, out)
        scanblock(n.body, out)
    end
    for _, name in ipairs(decls(n)) do out[name] = nil end
    return out
end

local function children(n, threshold)
    if n.kind == "if" then
        for _, x in ipairs(n.branches or {}) do pass.run(x.body, threshold) end
        if n.elsebody then pass.run(n.elsebody, threshold) end
    elseif n.body then
        pass.run(n.body, threshold)
    end
end

function pass.run(block, threshold)
    threshold = math.floor(tonumber(threshold) or 0)
    for _, n in ipairs(block.body or {}) do children(n, threshold) end
    if threshold <= 0 or #(block.body or {}) < 2 then return block end

    local body = block.body
    local used = {}
    for i, n in ipairs(body) do used[i] = refs(n) end

    local last = {}
    for i = #body, 1, -1 do
        for name in pairs(used[i]) do
            if last[name] == nil then last[name] = i end
        end
    end

    local ranges = {}
    local start = nil
    local count = 0
    local finish = 0
    for i, n in ipairs(body) do
        local ds = decls(n)
        if #ds > 0 then
            if not start then start = i end
            count += #ds
            for _, name in ipairs(ds) do
                local x = last[name] or i
                if x > finish then finish = x end
            end
        end
        if start and i >= finish and count >= threshold then
            ranges[#ranges + 1] = { start, i }
            start = nil
            count = 0
            finish = 0
        end
    end

    if #ranges == 0 then return block end
    local by = {}
    for _, r in ipairs(ranges) do by[r[1]] = r[2] end
    local out = {}
    local i = 1
    while i <= #body do
        local e = by[i]
        if e then
            local sub = { kind = "block", body = {} }
            for j = i, e do sub.body[#sub.body + 1] = body[j] end
            out[#out + 1] = { kind = "do", body = sub }
            i = e + 1
        else
            out[#out + 1] = body[i]
            i += 1
        end
    end
    block.body = out
    return block
end

return pass
