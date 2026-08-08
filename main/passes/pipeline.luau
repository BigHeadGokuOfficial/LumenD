

local dead = require("main.passes.deadcode")
local names = require("main.passes.names")
local prov = require("main.passes.provenance")
local inline = require("main.passes.inline")
local cond = require("main.passes.conditions")
local flow = require("main.passes.flow")

local pipe = {}

function pipe.run(ir, opt, check)
    opt = opt or {}


    if check then check() end
    if opt.dce ~= false then dead.run(ir, check) end
    if check then check() end


    names.run(ir)
    if check then check() end
    if opt.smartnames ~= false then
        prov.run(ir)
        if check then check() end
    else
        ir.bestname, ir.namescore, ir.hints, ir.origin = {}, {}, {}, {}
    end

    if opt.inline ~= false then inline.run(ir, check) end
    if check then check() end
    cond.run(ir)
    if check then check() end
    flow.run(ir)
    if check then check() end
    return ir
end

return pipe
