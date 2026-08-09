local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local branch = {}


local function graphinfo(st, pc, stop)
    local bid = st.cfg.blockmap[pc]
    local block = bid and st.cfg.blocks[bid]
    local structure = st.cfg.structure
    local region = structure and structure.byHeader and structure.byHeader[bid]
    local op = st.proto.Instructions[pc]
    if not block or block.endPC ~= pc or not region or not op or not ins.isConditional(op) then return nil end

    local joinpc = region.joinPC
    if not joinpc or joinpc <= pc or joinpc > stop then return nil end
    local jumppc, fallpc = ins.jumpTarget(pc, op), st:next(pc)
    local jumpbid, fallbid = st.cfg.blockmap[jumppc], st.cfg.blockmap[fallpc]

    if region.kind == "triangle" then
        local bodybid = region.thenBlock
        local body = bodybid and st.cfg.blocks[bodybid]
        if not body or body.startPC <= pc or body.startPC >= joinpc then return nil end
        if st.cfg.ipdom[bodybid] ~= region.join then return nil end
        local condition
        if jumpbid == bodybid and fallbid == region.join then condition = cond.jump(st, pc, op)
        elseif fallbid == bodybid and jumpbid == region.join then condition = cond.fall(st, pc, op)
        else return nil end
        return {
            cond = condition, a = body.startPC, b = joinpc, join = joinpc,
            head = pc, last = pc, condpcs = { pc }, graph = true, region = region,
        }
    elseif region.kind == "diamond" then
        local ab, bb = st.cfg.blocks[region.thenBlock], st.cfg.blocks[region.elseBlock]
        if not ab or not bb then return nil end
        if st.cfg.ipdom[ab.id] ~= region.join or st.cfg.ipdom[bb.id] ~= region.join then return nil end
        local first, second = ab, bb
        if second.startPC < first.startPC then first, second = second, first end
        if first.startPC <= pc or second.startPC <= first.startPC or second.startPC >= joinpc then return nil end
        local condition
        if jumpbid == first.id then condition = cond.jump(st, pc, op)
        elseif fallbid == first.id then condition = cond.fall(st, pc, op)
        else return nil end
        return {
            cond = condition, a = first.startPC, b = second.startPC,
            c = second.startPC, d = joinpc, join = joinpc,
            head = pc, last = pc, condpcs = { pc }, graph = true, region = region,
        }
    end
end

function branch.info(st, pc, stop)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return graphinfo(st, pc, stop) end

    local join = st:join(pc)

    if not join or join <= pc or join > stop then return graphinfo(st, pc, stop) end
    if ch.exit > join then return graphinfo(st, pc, stop) end

    if ch.exit == join then
        return { cond = ch.cond, a = ch.body, b = join, join = join, head = pc, last = ch.last, condpcs = ch.pcs }
    end
    return { cond = ch.cond, a = ch.body, b = ch.exit, c = ch.exit, d = join, join = join, head = pc, last = ch.last, condpcs = ch.pcs }
end

function branch.elseifInfo(st, pc, join)
    local op = st.proto.Instructions[pc]
    if not op or not ins.isConditional(op) then return nil end
    local sub = branch.info(st, pc, join)
    if sub and sub.join == join then return sub end
end

return branch
