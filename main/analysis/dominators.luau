local dom = {}

local function equal(a, b)
    for key in pairs(a) do if not b[key] then return false end end
    for key in pairs(b) do if not a[key] then return false end end
    return true
end

function dom.compute(blocks)
    local all = {}
    for _, block in ipairs(blocks) do all[block.id] = true end

    local out = {}
    for _, block in ipairs(blocks) do
        local set = {}

        if block.id == 1 then
            set[1] = true
        else
            for id in pairs(all) do set[id] = true end
        end

        out[block.id] = set
    end

    local chg = true
    while chg do
        chg = false

        for _, block in ipairs(blocks) do
            if block.id ~= 1 then
                local set = nil

                for _, pred in ipairs(block.predecessors) do
                    local predSet = out[pred]

                    if set == nil then
                        set = {}
                        for id in pairs(predSet) do set[id] = true end
                    else
                        for id in pairs(set) do
                            if not predSet[id] then set[id] = nil end
                        end
                    end
                end

                set = set or {}
                set[block.id] = true

                if not equal(out[block.id], set) then
                    out[block.id] = set
                    chg = true
                end
            end
        end
    end

    return out
end

return dom