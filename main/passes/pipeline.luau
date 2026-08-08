local simp = require("main.passes.simplify")
local konst = require("main.passes.constants")
local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt)
    opt = opt or {}
    simp.run(ir)
    if opt.fold ~= false then konst.run(ir) end
    if opt.dce ~= false then dead.run(ir) end
    names.run(ir)
    if opt.smartnames ~= false then prov.run(ir) else ir.bestname, ir.namescore, ir.hints, ir.origin = {}, {}, {}, {} end
    if opt.inline ~= false then inline.run(ir) end
    cond.run(ir)
    flow.run(ir)
    return ir
end

return pipe