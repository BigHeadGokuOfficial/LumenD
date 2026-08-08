local post = {}

local function rpo(blocks)
    local n = #blocks
    local root = n + 1
    local exits = {}

    for _, b in ipairs(blocks) do
        if #b.successors == 0 then exits[#exits + 1] = b.id end
    end

    local seen = { [root] = true }
    local postorder = {}
    local stack = { { id = root, i = 1 } }

    local function nexts(id)
        if id == root then return exits end
        return blocks[id].predecessors
    end

    while #stack > 0 do
        local top = stack[#stack]
        local list = nexts(top.id)
        local sid = list[top.i]

        if sid then
            top.i += 1
            if not seen[sid] then
                seen[sid] = true
                stack[#stack + 1] = { id = sid, i = 1 }
            end
        else
            postorder[#postorder + 1] = top.id
            stack[#stack] = nil
        end
    end

    local out = {}
    for i = #postorder, 1, -1 do out[#out + 1] = postorder[i] end
    return out, seen, root, exits
end

local function meet(a, b, idom, rank)
    while a ~= b do
        while rank[a] > rank[b] do a = idom[a] end
        while rank[b] > rank[a] do b = idom[b] end
    end
    return a
end

function post.run(blocks)
    if #blocks == 0 then return {}, {} end

    local order, reach, root = rpo(blocks)
    local rank = {}
    for i, id in ipairs(order) do rank[id] = i end

    local idom = { [root] = root }
    local changed = true

    while changed do
        changed = false

        for i = 2, #order do
            local id = order[i]
            local succ = blocks[id].successors
            local first

            if #succ == 0 then
                first = root
            else
                for _, sid in ipairs(succ) do
                    if idom[sid] then
                        first = sid
                        break
                    end
                end
            end

            if first then
                local new = first

                if #succ > 0 then
                    for _, sid in ipairs(succ) do
                        if sid ~= first and idom[sid] then
                            new = meet(sid, new, idom, rank)
                        end
                    end
                end

                if idom[id] ~= new then
                    idom[id] = new
                    changed = true
                end
            end
        end
    end

    local pd = {}
    local ip = {}

    for _, b in ipairs(blocks) do
        local set = { [b.id] = true }

        if reach[b.id] then
            local cur = b.id
            local parent = idom[cur]
            if parent and parent ~= root and parent ~= cur then ip[b.id] = parent end

            local guard = 0
            while parent and parent ~= root and parent ~= cur and guard <= #blocks do
                set[parent] = true
                cur = parent
                parent = idom[cur]
                guard += 1
            end
        end

        pd[b.id] = set
    end

    return pd, ip
end

return post
