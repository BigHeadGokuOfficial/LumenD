local statements = require("main.ast.statements")
local normalize = require("main.ast.normalize")
local logic = require("main.ast.logic")
local fold = require("main.ast.fold")
local conditions = require("main.ast.conditions")
local locals = require("main.ast.locals")
local place = require("main.ast.place_locals")
local guards = require("main.ast.guards2")
local selects = require("main.ast.selects")
local returns = require("main.ast.returns")
local booleans = require("main.ast.booleans")
local inline = require("main.ast.inline")
local callbacks = require("main.ast.callbacks")
local compound = require("main.ast.compound")
local deadcode = require("main.ast.deadcode")
local doblocks = require("main.ast.doblocks")

local pass = {}

function pass.run(root, opt)
    opt = opt or {}

    statements.run(root)
    normalize.run(root, opt)
    logic.run(root)

    if opt.fold ~= false then fold.run(root) end
    if opt.conditions ~= false then conditions.run(root) end

    normalize.run(root, opt)
    locals.run(root)
    if opt.fidelity == false then place.run(root) end
    normalize.run(root, opt)

    if opt.guards == true then
        guards.run(root)
        normalize.run(root, opt)
        if opt.fidelity == false then place.run(root) end
        normalize.run(root, opt)
    end

    if opt.selects == true then selects.run(root) end
    if opt.returns == true then returns.run(root) end
    if opt.booleans == true then booleans.run(root) end
    if opt.compound == true then compound.run(root) end

    if opt.inlineast == true then inline.run(root) end
    if opt.callbacks == true then callbacks.run(root) end
    if (tonumber(opt.doblocks) or 0) > 0 then doblocks.run(root, opt.doblocks) end
    if opt.fidelity == false and opt.dce ~= false then deadcode.run(root) end

    statements.run(root)
    normalize.run(root, opt)
    logic.run(root)
    return root
end

return pass
