

local dead = require("main.passes.deadcode")
local simplify = require("main.passes.simplify")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt, check)
    opt = opt or {}
    ir.timings = ir.timings or {}
    local pt = ir.timings.passes or {}
    ir.timings.passes = pt
    local t

    if check then check() end
    if opt.dce ~= false then t = os.clock(); dead.run(ir, check); pt.deadcode = os.clock() - t end
    if check then check() end
    t = os.clock(); simplify.run(ir); pt.simplify = os.clock() - t
    if check then check() end

    t = os.clock(); names.run(ir); pt.outssa = os.clock() - t
    if check then check() end
    if opt.smartnames ~= false then
        t = os.clock(); prov.run(ir); pt.naming = os.clock() - t
        if check then check() end
    else
        ir.bestname, ir.namescore, ir.hints, ir.origin = {}, {}, {}, {}
        pt.naming = 0
    end

    if opt.inline ~= false then t = os.clock(); inline.run(ir, check); pt.inline = os.clock() - t end
    if check then check() end
    t = os.clock(); cond.run(ir); pt.conditions = os.clock() - t
    if check then check() end
    t = os.clock(); flow.run(ir); pt.flow = os.clock() - t
    if check then check() end
    return ir
end

return pipe
