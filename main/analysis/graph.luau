local ins = require("main.bytecode.instructions")
local regs = require("main.analysis.registers")
local dom = require("main.analysis.dominators")
local loops = require("main.analysis.loops")
local post = require("main.analysis.postdom")

local graph = {}

function graph.build(proto)
    local ops = proto.Instructions
    local aux = ins.auxSlots(proto)
    local leaders = { [1] = true }
    local nexts = {}

    local function valid(pc)
        return pc >= 1 and pc <= #ops and not aux[pc]
    end

    for pc = 1, #ops do
        if not aux[pc] then
            local op = ops[pc]
            local name = ins.name(op)
            local nextPC = ins.next(proto, pc, aux)
            local successors = {}

            if name == "RETURN" then

            elseif name == "LOADB" and (op.C or 0) ~= 0 then
                local target = pc + op.C + 1
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            elseif ins.isConditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then successors[#successors + 1] = nextPC; leaders[nextPC] = true end

            elseif ins.isUnconditional(op) then
                local target = ins.jumpTarget(pc, op)
                if valid(target) then successors[#successors + 1] = target; leaders[target] = true end
                if valid(nextPC) then leaders[nextPC] = true end

            else
                if valid(nextPC) then successors[#successors + 1] = nextPC end
            end

            nexts[pc] = successors
        end
    end

    local list = {}
    for pc in pairs(leaders) do if valid(pc) then list[#list + 1] = pc end end
    table.sort(list)

    local blocks = {}
    local blockmap = {}

    for index, startPC in ipairs(list) do
        local nextLeader = list[index + 1] or (#ops + 1)
        local pcs = {}

        for pc = startPC, nextLeader - 1 do
            if not aux[pc] then
                pcs[#pcs + 1] = pc
                blockmap[pc] = index
            end
        end

        blocks[index] = {
            id = index,
            startPC = startPC,
            endPC = pcs[#pcs] or startPC,
            pcs = pcs,
            successors = {},
            predecessors = {},
        }
    end

    for _, block in ipairs(blocks) do
        local seen = {}
        for _, nextpc in ipairs(nexts[block.endPC] or {}) do
            local nextblock = blockmap[nextpc]
            if nextblock and not seen[nextblock] then
                seen[nextblock] = true
                block.successors[#block.successors + 1] = nextblock
            end
        end
    end

    for _, block in ipairs(blocks) do
        for _, successor in ipairs(block.successors) do
            blocks[successor].predecessors[#blocks[successor].predecessors + 1] = block.id
        end
    end

    local dominators = dom.compute(blocks)
    local postdom, ipdom = post.run(blocks)

    return {
        proto = proto,
        aux = aux,
        blocks = blocks,
        blockmap = blockmap,
        nexts = nexts,
        dominators = dominators,
        postdom = postdom,
        ipdom = ipdom,
        loops = loops.find(blocks, dominators),
        registerStats = regs.stats(proto, aux),
    }
end

return graph