local graph = require("main.analysis.graph")
local ssa = require("main.analysis.ssa")
local irbuild = require("main.ir.build")
local passes = require("main.passes.pipeline")

local view = {}

function view.graph(data)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    return graph.build(proto)
end

function view.ssa(data)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    local cfg = graph.build(proto)
    return ssa.build(proto, cfg)
end

function view.ir(data, opt)
    local proto = assert(data.Protos[data.ProtoEntryPoint], "missing entry proto")
    return passes.run(irbuild.run(proto), opt or {})
end

return view