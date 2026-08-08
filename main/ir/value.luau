local val = {}
val.__index = val

function val.new(id, src)
    return setmetatable({
        id = id,
        reg = src.reg,
        pc = src.pc,
        block = src.block,
        kind = src.kind,
        dead = src.dead == true,
        alias = nil,
        uses = {},
        const = nil,
        inline = false,
    }, val)
end

return val
