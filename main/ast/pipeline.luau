local fold = require("main.ast.fold")
local cond = require("main.ast.conditions")
local logic = require("main.ast.logic")
local guards = require("main.recover.guards")
local guards2 = require("main.ast.guards2")
local selectp = require("main.ast.selects")
local ret = require("main.ast.returns")
local inline = require("main.ast.inline")
local callbacks = require("main.ast.callbacks")
local bools = require("main.ast.booleans")
local comp = require("main.ast.compound")
local locals = require("main.ast.locals")
local dead = require("main.ast.deadcode")

local pass = {}

function pass.run(root, opt)
    opt = opt or {}
    if opt.dce ~= false then dead.run(root) end
    if opt.fold ~= false then fold.run(root) end
    if opt.conditions ~= false then cond.run(root) end
    if opt.selects ~= false then selectp.run(root) end
    if opt.returns ~= false then ret.run(root) end
    if opt.inlineast ~= false then inline.run(root) end
    if opt.callbacks ~= false then callbacks.run(root) end
    if opt.booleans ~= false then bools.run(root) end
    if opt.guards ~= false then
        guards2.run(root)
        guards.run(root)
    end
    locals.run(root)
    if opt.compound ~= false then comp.run(root) end
    logic.run(root)
    if opt.conditions ~= false then cond.run(root) end
    if opt.dce ~= false then dead.run(root) end
    return root
end

return pass