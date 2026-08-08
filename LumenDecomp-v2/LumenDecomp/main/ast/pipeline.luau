local fold = require("main.ast.fold")
local cond = require("main.ast.conditions")
local guards = require("main.recover.guards")
local locals = require("main.ast.locals")
local dead = require("main.ast.deadcode")

local pass = {}

function pass.run(root, opt)
    opt = opt or {}
    if opt.fold ~= false then fold.run(root) end
    if opt.conditions ~= false then cond.run(root) end
    if opt.guards ~= false then guards.run(root) end
    locals.run(root)
    if opt.dce ~= false then dead.run(root) end
    return root
end

return pass
