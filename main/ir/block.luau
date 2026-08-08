
local block = {}
block.__index = block

function block.new(src)
    return setmetatable({
        id = src.id,
        first = src.startPC,
        last = src.endPC,
        pcs = src.pcs,
        preds = src.predecessors,
        succs = src.successors,
        ops = {},
    }, block)
end

return block
