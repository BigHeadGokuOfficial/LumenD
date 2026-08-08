
local post = {}

local function clone(s)
    local out = {}
    for k in pairs(s) do out[k] = true end
    return out
end

local function same(a, b)
    for k in pairs(a) do if not b[k] then return false end end
    for k in pairs(b) do if not a[k] then return false end end
    return true
end

local function intersectinto(dst, src)
    for k in pairs(dst) do
        if not src[k] then dst[k] = nil end
    end
end

function post.run(blocks, check)
    local exitid = #blocks + 1
    local all = { [exitid] = true }
    for _, b in ipairs(blocks) do all[b.id] = true end

    local pd = { [exitid] = { [exitid] = true } }
    for _, b in ipairs(blocks) do pd[b.id] = clone(all) end

    local dirty = true
    local iterations = 0
    local limit = math.max(64, (#blocks + 1) * (#blocks + 1) * 4)
    while dirty do
        if check then check() end
        iterations += 1
        if iterations > limit then
            error("LumenV4: post-dominator analysis failed to converge", 2)
        end
        dirty = false

        for i = #blocks, 1, -1 do
            local b = blocks[i]
            local succ = b.successors
            local set

            if #succ == 0 then
                set = clone(pd[exitid])
            else
                for _, sid in ipairs(succ) do
                    local src = assert(pd[sid], "LumenV4: invalid postdom successor " .. tostring(sid))
                    if not set then set = clone(src) else intersectinto(set, src) end
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

    local ip = {}
    for _, b in ipairs(blocks) do
        if check then check() end
        local cand = {}
        for id in pairs(pd[b.id]) do
            if id ~= b.id then cand[#cand + 1] = id end
        end
        table.sort(cand)

        for _, id in ipairs(cand) do
            local immediate = true

            for _, other in ipairs(cand) do
                if other ~= id and pd[other] and pd[other][id] then
                    immediate = false
                    break
                end
            end
            if immediate then
                ip[b.id] = id
                break
            end
        end
    end

    return pd, ip, exitid
end

return post
