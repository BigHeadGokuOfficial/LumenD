local ins = require("main.bytecode.instructions")

local pass = {}

function pass.run(ir)
    local out = {}
    for _, n in ipairs(ir.ops) do
        if ins.isConditional(n.op) then
            out[n.pc] = {
                jump = ins.jumpTarget(n.pc, n.op),
                fall = ins.next(ir.proto, n.pc, ir.cfg.aux),
                block = n.block,
                join = ir.cfg.ipdom[n.block],
            }
        end
    end
    ir.conds = out
    return ir
end

return pass