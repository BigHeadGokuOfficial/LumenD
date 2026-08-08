local ins = require("main.bytecode.instructions")
local cond = require("main.recover.conditions")

local loops = {}

function loops.whileInfo(st, pc)
    local ch = cond.chain(st, pc)
    if not ch or ch.exit <= ch.body then return nil end
    local latch = ins.previousRealPC(st.cfg.aux, ch.exit)
    if not latch then return nil end
    local op = st.proto.Instructions[latch]
    local name = ins.name(op)
    if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(latch, op) <= pc then
        return { cond = ch.cond, body = ch.body, bodyend = latch, exit = ch.exit, cont = pc }
    end
end

function loops.repeatInfo(st, pc)
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc then
            local op = st.proto.Instructions[loop.latchPC]
            if ins.isConditional(op) and ins.jumpTarget(loop.latchPC, op) == pc then
                return { body = pc, latch = loop.latchPC, exit = st:next(loop.latchPC), cont = loop.latchPC }
            end
        end
    end
end

function loops.foreverInfo(st, pc, stop)
    local head = st.proto.Instructions[pc]
    if ins.isConditional(head) then return nil end
    for _, loop in ipairs(st.cfg.loops) do
        if loop.headerPC == pc and loop.latchPC > pc and loop.latchPC < stop then
            local op = st.proto.Instructions[loop.latchPC]
            local name = ins.name(op)
            if (name == "JUMP" or name == "JUMPBACK" or name == "JUMPX") and ins.jumpTarget(loop.latchPC, op) == pc then
                local exit = loop.exitPC
                if not exit then
                    for _, ep in ipairs(loop.exits or {}) do
                        if ep > loop.latchPC and (not exit or ep < exit) then exit = ep end
                    end
                end
                exit = exit or st:next(loop.latchPC)
                return { body = pc, latch = loop.latchPC, exit = exit, cont = pc }
            end
        end
    end
end

function loops.numInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORNLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

function loops.genInfo(st, pc, op, stop)
    local loop = ins.jumpTarget(pc, op)
    if loop <= pc or loop >= stop then return nil end
    local lop = st.proto.Instructions[loop]
    if ins.name(lop) ~= "FORGLOOP" or lop.A ~= op.A then return nil end
    return { loop = loop, op = lop, exit = st:next(loop) }
end

return loops
