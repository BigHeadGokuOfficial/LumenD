local dom = {}

local function rpo(blocks)
    local seen = {}
    local post = {}
    local stack = { { id = 1, i = 1 } }
    seen[1] = true

    while #stack > 0 do
        local top = stack[#stack]
        local b = blocks[top.id]
        local sid = b and b.successors[top.i]

        if sid then
            top.i += 1
            if not seen[sid] then
                seen[sid] = true
                stack[#stack + 1] = { id = sid, i = 1 }
            end
        else
            post[#post + 1] = top.id
            stack[#stack] = nil
        end
    end

    local out = {}
    for i = #post, 1, -1 do out[#out + 1] = post[i] end
    return out, seen
end

local function meet(a, b, idom, rank)
    while a ~= b do
        while rank[a] > rank[b] do a = idom[a] end
        while rank[b] > rank[a] do b = idom[b] end
    end
    return a
end

function dom.compute(blocks)
    if #blocks == 0 then return {} end

    local order, reach = rpo(blocks)
    local rank = {}
    for i, id in ipairs(order) do rank[id] = i end

    local idom = { [1] = 1 }
    local changed = true

    while changed do
        changed = false

        for i = 2, #order do
            local id = order[i]
            local b = blocks[id]
            local first

            for _, pid in ipairs(b.predecessors) do
                if idom[pid] then
                    first = pid
                    break
                end
            end

            if first then
                local new = first
                for _, pid in ipairs(b.predecessors) do
                    if pid ~= first and idom[pid] then
                        new = meet(pid, new, idom, rank)
                    end
                end

                if idom[id] ~= new then
                    idom[id] = new
                    changed = true
                end
            end
        end
    end

    local out = {}
    for _, b in ipairs(blocks) do
        local set = { [b.id] = true }

        if reach[b.id] then
            local cur = b.id
            local guard = 0
            while cur ~= 1 and idom[cur] and guard <= #blocks do
                cur = idom[cur]
                set[cur] = true
                guard += 1
            end
        end

        out[b.id] = set
    end

    out.idom = idom
    return out
end

return dom
