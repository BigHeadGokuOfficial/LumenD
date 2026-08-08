
local loops = {}

function loops.find(blocks, dom)
    local out = {}

    for _, latch in ipairs(blocks) do
        for _, hid in ipairs(latch.successors) do
            if dom[latch.id] and dom[latch.id][hid] then
                local set = { [hid] = true, [latch.id] = true }
                local todo = { latch.id }
                local n = 1

                while n <= #todo do
                    local id = todo[n]
                    n += 1
                    for _, pid in ipairs(blocks[id].predecessors) do
                        if not set[pid] then
                            set[pid] = true
                            if pid ~= hid then todo[#todo + 1] = pid end
                        end
                    end
                end

                local exits = {}
                local seen = {}
                for id in pairs(set) do
                    for _, sid in ipairs(blocks[id].successors) do
                        if not set[sid] and not seen[sid] then
                            seen[sid] = true
                            exits[#exits + 1] = blocks[sid].startPC
                        end
                    end
                end
                table.sort(exits)

                out[#out + 1] = {
                    header = hid,
                    latch = latch.id,
                    headerPC = blocks[hid].startPC,
                    latchPC = latch.endPC,
                    nodes = set,
                    exits = exits,
                    exitPC = #exits == 1 and exits[1] or nil,
                }
            end
        end
    end

    return out
end

return loops
