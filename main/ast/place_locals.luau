local expr = require("main.output.expr")

local pass = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hit(text, name)
    if type(text) ~= "string" then return false end
    return text:find("%f[%w_]" .. esc(name) .. "%f[^%w_]") ~= nil
end

local function nodeown(node, name)
    if not node or node.dead then return false end
    if hit(node.text, name) or hit(node.cond, name) or hit(node.head, name)
        or hit(node.args, name) or hit(node.pre, name) or hit(node.post, name) then
        return true
    end
    for _, n in ipairs(node.names or {}) do if n == name then return true end end
    for _, value in ipairs(node.values or {}) do
        if hit(expr.str(value), name) then return true end
    end
    if node.kind == "if" then
        for _, branch in ipairs(node.branches or {}) do
            if hit(branch.cond, name) then return true end
        end
    end
    return false
end

local function deepnode(node, name)
    if nodeown(node, name) then return true end
    if node.kind == "if" then
        for _, branch in ipairs(node.branches or {}) do
            for _, child in ipairs(branch.body.body or {}) do
                if deepnode(child, name) then return true end
            end
        end
        if node.elsebody then
            for _, child in ipairs(node.elsebody.body or {}) do
                if deepnode(child, name) then return true end
            end
        end
    elseif node.body then
        for _, child in ipairs(node.body.body or {}) do
            if deepnode(child, name) then return true end
        end
    end
    return false
end

local function children(node)
    local out = {}
    if node.kind == "if" then
        for _, branch in ipairs(node.branches or {}) do
            out[#out + 1] = { block = branch.body, loop = false }
        end
        if node.elsebody then out[#out + 1] = { block = node.elsebody, loop = false } end
    elseif node.kind == "while" or node.kind == "repeat" or node.kind == "for" then
        out[#out + 1] = { block = node.body, loop = true }
    elseif node.kind == "do" then
        out[#out + 1] = { block = node.body, loop = false }
    end
    return out
end

local function splitdecls(block)
    local out = {}
    for _, node in ipairs(block.body or {}) do
        if node.kind == "decl" and #(node.names or {}) > 1 then
            for i, name in ipairs(node.names) do
                out[#out + 1] = {
                    kind = "decl",
                    names = { name },
                    symbols = node.symbols and { node.symbols[i] } or nil,
                    annotations = node.annotations and { [1] = node.annotations[i] } or nil,
                }
            end
        else
            out[#out + 1] = node
        end
    end
    block.body = out
end

local function buildparents(block, parent, crossedloop, parents, loops)
    parents[block] = parent
    loops[block] = crossedloop == true
    for _, node in ipairs(block.body or {}) do
        if node.kind ~= "function" and node.kind ~= "callback" then
            for _, child in ipairs(children(node)) do
                buildparents(child.block, block, child.loop, parents, loops)
            end
        end
    end
end

local function ancestors(block, parents)
    local out = {}
    local cur, depth = block, 0
    while cur do
        out[cur] = depth
        cur = parents[cur]
        depth += 1
    end
    return out
end

local function lca(blocks, parents)
    if #blocks == 0 then return nil end
    local common = ancestors(blocks[1], parents)
    for i = 2, #blocks do
        local seen = ancestors(blocks[i], parents)
        for block in pairs(common) do
            if seen[block] == nil then common[block] = nil end
        end
    end

    local best, bestdepth
    local first = ancestors(blocks[1], parents)
    for block in pairs(common) do
        local depth = first[block]
        if depth ~= nil and (bestdepth == nil or depth < bestdepth) then
            best, bestdepth = block, depth
        end
    end
    return best
end

local function crossesloop(from, to, parents, loops)
    local cur = to
    while cur and cur ~= from do
        if loops[cur] then return true end
        cur = parents[cur]
    end
    return cur ~= from
end

local function gather(block, startat, name, uses)
    for i = startat or 1, #(block.body or {}) do
        local node = block.body[i]
        if node and not node.dead then
            if node.kind == "function" or node.kind == "callback" then
                -- Captures count as a use at the closure-creation site.
                if deepnode(node, name) then uses[#uses + 1] = block end
            else
                if nodeown(node, name) then uses[#uses + 1] = block end
                for _, child in ipairs(children(node)) do
                    gather(child.block, 1, name, uses)
                end
            end
        end
    end
end

local function firstdeepuse(block, startat, name)
    for i = startat, #(block.body or {}) do
        if deepnode(block.body[i], name) then return i end
    end
end

local function processfunction(root)
    local parents, loops = {}, {}
    buildparents(root, nil, false, parents, loops)

    local function processblock(block)
        splitdecls(block)

        local candidates = {}
        for i, node in ipairs(block.body or {}) do
            if node.kind == "decl" and #(node.names or {}) == 1 then
                candidates[#candidates + 1] = {
                    index = i,
                    node = node,
                    name = node.names[1],
                }
            end
        end

        -- Reverse order keeps stored indices stable while declarations move/remove.
        for ci = #candidates, 1, -1 do
            local candidate = candidates[ci]
            if block.body[candidate.index] == candidate.node then
                local uses = {}
                gather(block, candidate.index + 1, candidate.name, uses)
                local destination = lca(uses, parents)

                if destination and destination ~= block
                    and not crossesloop(block, destination, parents, loops) then
                    table.remove(block.body, candidate.index)
                    table.insert(destination.body, 1, candidate.node)
                elseif destination == block then
                    -- Medal-style "latest safe statement" approximation:
                    -- uninitialized locals can move immediately before the first
                    -- top-level construct that references them.
                    local first = firstdeepuse(block, candidate.index + 1, candidate.name)
                    if first and first > candidate.index + 1 then
                        table.remove(block.body, candidate.index)
                        table.insert(block.body, first - 1, candidate.node)
                    end
                end
            end
        end

        for _, node in ipairs(block.body or {}) do
            if node.kind == "function" or node.kind == "callback" then
                processfunction(node.body)
            else
                for _, child in ipairs(children(node)) do
                    processblock(child.block)
                end
            end
        end
    end

    processblock(root)
end

function pass.run(root)
    processfunction(root)
    return root
end

return pass
