local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local join = st:join(pc)
    if not join or join <= pc or join > stop then join = ch.exit end
    if ch.exit > join then return nil end

    if ch.exit == join then
        return { cond = ch.cond, a = ch.body, b = join, join = join }
    end

    return { cond = ch.cond, a = ch.body, b = ch.exit, c = ch.exit, d = join, join = join }
end

function branch.elseifInfo(st, pc, join)
    local op = st.proto.Instructions[pc]
    if not op or not ins.isConditional(op) then return nil end
    local sub = branch.info(st, pc, join)
    if sub and sub.join == join then return sub end
end

return branch