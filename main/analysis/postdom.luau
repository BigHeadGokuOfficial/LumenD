local post = {}

local function same(a, b)
    for k in pairs(a) do
        if not b[k] then return false end
    end
    for k in pairs(b) do
        if not a[k] then return false end
    end
    return true
end

function post.run(blocks)
    local all = {}
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = {}
    for _, b in ipairs(blocks) do
        local set = {}
        if #b.successors == 0 then
            set[b.id] = true
        else
            for id in pairs(all) do set[id] = true end
        end
        pd[b.id] = set
    end

    local dirty = true
    while dirty do
        dirty = false
        for i = #blocks, 1, -1 do
            local b = blocks[i]
            if #b.successors > 0 then
                local set
                for _, sid in ipairs(b.successors) do
                    local src = pd[sid]
                    if not set then
                        set = {}
                        for id in pairs(src) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not src[id] then set[id] = nil end
                        end
                    end
                end
                set = set or {}
                set[b.id] = true
                if not same(pd[b.id], set) then
                    pd[b.id] = set
                    dirty = true
                end
            end
        end
    end

    local ip = {}
    for _, b in ipairs(blocks) do
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        for _, id in ipairs(cand) do
            local near = true
            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    near = false
                    break
                end
            end
            if near then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip
end

return post