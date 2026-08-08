local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local regs = require("main.analysis.registers")
local ins = require("main.bytecode.instructions")
local fx = require("main.ir.effects")
local fn = require("main.ir.function")
local val = require("main.ir.value")
local block = require("main.ir.block")

local build = {}

function build.run(proto)
    local cfg = graph.build(proto)
    local flow = ssa.build(proto, cfg)
    local out = fn.new(proto, cfg, flow)

    for id, src in ipairs(flow.versions) do
        out.vals[id] = val.new(id, src)
        if src.dead then out.dead[id] = true end
    end

    for bid, phis in pairs(flow.phisByBlock) do
        local dst = {}
        out.phis[bid] = dst
        for reg, p in pairs(phis) do
            dst[reg] = { id = p.id, reg = reg, inputs = p.inputs, missing = p.missing }
        end
    end

    for _, src in ipairs(cfg.blocks) do
        local b = block.new(src)
        out.blocks[b.id] = b
        for _, pc in ipairs(src.pcs) do
            local op = proto.Instructions[pc]
            local name = cfg.names and cfg.names[pc] or ins.name(op)
            local pair = cfg.rw and cfg.rw[pc]
            local reads, writes
            if pair then
                reads, writes = pair.reads, pair.writes
            else
                reads, writes = regs.readWrite(op)
            end
            local n = {
                pc = pc,
                op = op,
                name = name,
                block = b.id,
                reads = reads,
                writes = writes,
                pure = fx.pure(name),
                drop = fx.drop(name),
                quiet = fx.quiet(name),
                effect = fx.effect(name),
                term = fx.term(name),
            }
            out.ops[#out.ops + 1] = n
            out.bypc[pc] = n
            b.ops[#b.ops + 1] = n
        end
    end

    out:reindex()
    return out
end

return build