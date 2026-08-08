local lit = require("main.output.literals")
local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local ty = require("main.naming.types")
local dbg = require("main.naming.debug_names")
local words = require("main.naming.words")
local ins = require("main.bytecode.instructions")

local pass = {}

local weak = {
    value = true, result = true, data = true, item = true, obj = true,
    num = true, text = true, flag = true, fn = true,
}

local owner = {
    Character = "player", Backpack = "player", PlayerGui = "player", PlayerScripts = "player",
    UserId = "player", Team = "player", TeamColor = "player", AccountAge = "player",
    Humanoid = "character", HumanoidRootPart = "character", PrimaryPart = "model",
    Health = "humanoid", MaxHealth = "humanoid", WalkSpeed = "humanoid", JumpPower = "humanoid",
    HipHeight = "humanoid", MoveDirection = "humanoid", FloorMaterial = "humanoid",
    CFrame = "part", Position = "part", Orientation = "part", Anchored = "part",
    CanCollide = "part", AssemblyLinearVelocity = "part", AssemblyAngularVelocity = "part",
    CameraType = "camera", CameraSubject = "camera", ViewportSize = "camera",
    AbsolutePosition = "gui", AbsoluteSize = "gui", BackgroundColor3 = "gui", Text = "gui",
    UserInputType = "input", KeyCode = "input", UserInputState = "input", Delta = "input",
    OnClientEvent = "remoteEvent", OnServerEvent = "remoteEvent",
}

local methown = {
    Kick = "player", GetMouse = "player", LoadCharacter = "player",
    MoveTo = "humanoid", TakeDamage = "humanoid", ChangeState = "humanoid",
    Raycast = "workspace", GetPartsInPart = "workspace", GetPartBoundsInBox = "workspace",
    Connect = "signal", ConnectParallel = "signal", Once = "signal", Wait = "signal",
    FireServer = "remoteEvent", FireClient = "remoteEvent", FireAllClients = "remoteEvent",
    InvokeServer = "remoteFunction", InvokeClient = "remoteFunction",
    GetPlayers = "players", GetPlayerFromCharacter = "players",
    GetTagged = "collectionService", HasTag = "collectionService", AddTag = "collectionService", RemoveTag = "collectionService",
    JSONDecode = "httpService", JSONEncode = "httpService", GenerateGUID = "httpService",
}

local function getk(proto, n)
    return proto.Constants and proto.Constants[(n or 0) + 1]
end

local function rawk(proto, n)
    return lit.rawStringConstant(getk(proto, n))
end

local function cv(ir, v)
    v = ir:resolve(v)
    local x = v and ir.constval and ir.constval[v]
    if not x then return nil, false end
    return x.nilv and nil or x.v, true
end

function pass.run(ir)
    local hints = {}
    local origin = {}
    local pend = {}
    local dr = dbg.ranges(ir.proto)
    local tr = ty.ranges(ir.proto)

    local function fam(v)
        return v and ir:nameid(v) or nil
    end

    local function add(v, name, score, why)
        v = fam(v)
        name = id.clean(name)
        if not v or not name then return end
        if weak[name] then score -= 8 end
        local h = hints[v]
        if not h then h = {}; hints[v] = h end
        local old = h[name]
        if not old then
            h[name] = { score = score, why = why, hits = 1 }
        else
            old.hits = (old.hits or 1) + 1
            if score > old.score then old.score, old.why = score, why end
        end
    end

    local function seto(v, path, kind)
        v = ir:resolve(v)
        if v and path then origin[v] = { path = path, kind = kind } end
    end

    local function geto(v)
        v = ir:resolve(v)
        return v and origin[v] or nil
    end

    local function opname(v)
        v = ir:resolve(v)
        local x = v and ir.vals[v]
        local n = x and x.pc and ir.bypc[x.pc]
        return n and n.name or nil
    end

    for v, src in pairs(ir.vals) do
        if src.kind == "param" and ir.paramhints then add(v, ir.paramhints[src.reg + 1], 118, "context") end
        local p = src.kind == "param" and ty.param(ir.proto, src.reg) or nil
        if p then add(v, ty.hint(p), 74, "ptype") end
        local di = src.pc and dbg.at(dr, src.reg, src.pc) or nil
        if di then add(v, di.name, 120, "debug") end
        local ti = src.pc and ty.at(tr, src.reg, src.pc) or nil
        if ti then add(v, ty.hint(ti), 78, "type") end
    end

    local prep = {}
    for _, n in ipairs(ir.ops) do
        local op = n.op
        local name = n.name
        local pc = n.pc
        local defs = ir.ssa.defsByPC[pc] or {}
        local uses = ir.ssa.usesByPC[pc] or {}
        local function d(r) return ir:resolve(defs[r]) end
        local function u(r) return ir:resolve(uses[r]) end

        if name == "GETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            add(d(op.A), g, 104, "global")
            seto(d(op.A), g, "global")
        elseif name == "GETIMPORT" then
            local k = getk(ir.proto, op.D)
            local p = lit.rawStringConstant(k) or lit.constant(k)
            add(d(op.A), rbx.fromImport(p) or words.call(p), 108, "import")
            seto(d(op.A), p, "import")
        elseif name == "GETUPVAL" then
            local up = ir.proto.Upvalues and ir.proto.Upvalues[op.B + 1]
            local un = up and up.Name
            add(d(op.A), un, 112, "upvalue")
            seto(d(op.A), un, "upvalue")
        elseif name == "MOVE" then
            local so = geto(u(op.B))
            if so then
                seto(d(op.A), so.path, so.kind)
                add(d(op.A), words.call(so.path) or words.field(so.path), 76, "move")
            end
        elseif name == "GETTABLEKS" or name == "GETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "GETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            add(d(op.A), rbx.fromField(f) or words.field(f), 91, "field")
            add(u(op.B), owner[f], 70, "owner")
            local so = geto(u(op.B))
            if so and f then seto(d(op.A), so.path .. "." .. f, "field") else seto(d(op.A), f, "field") end
        elseif name == "GETTABLEN" then
            local so = geto(u(op.B))
            if so then add(d(op.A), words.iter(words.call(so.path) or so.path), 64, "index") end
        elseif name == "SETTABLEKS" or name == "SETUDATAKS" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "SETUDATAKS" then ai = bit32.band(ai, 0xffff) end
            local f = rawk(ir.proto, ai)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 116 or 44
            add(u(op.A), rbx.fromField(f) or words.field(f), sc, "store")
        elseif name == "SETGLOBAL" then
            local g = rawk(ir.proto, op.AuxValue and op.AuxValue.Value or 0)
            local sc = (opname(u(op.A)) == "NEWCLOSURE" or opname(u(op.A)) == "DUPCLOSURE") and 120 or 38
            add(u(op.A), g, sc, "gstore")
        elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
            local ai = op.AuxValue and op.AuxValue.Value or 0
            if name == "NAMECALLUDATA" then ai = bit32.band(ai, 0xffff) end
            local m = rawk(ir.proto, ai)
            pend[op.A] = { method = m, obj = u(op.B), pc = pc }
            add(u(op.B), methown[m], 72, "method-owner")
        elseif name == "CALL" or name == "CALLFB" then
            local p = pend[op.A]
            local out = d(op.A)
            local callpath
            if p then
                local arg
                if (op.B or 0) == 0 or op.B > 2 then arg = select(1, cv(ir, u(op.A + 2))) end
                local oo = geto(p.obj)
                local base = oo and oo.path or nil
                local h = rbx.fromMethod(p.method, arg) or words.method(p.method)
                if p.method == "Create" and base and base:match("TweenService$") then h = "tween" end
                if p.method == "Clone" and base then
                    local tail = base:match("([%a_][%w_]*)$")
                    if tail then h = words.clean(tail .. "Clone") end
                end
                if p.method == "Connect" or p.method == "ConnectParallel" or p.method == "Once" then h = "connection" end
                if p.method == "Wait" and base and base:match("Signal$") then h = "value" end
                add(out, h, 106, "method")
                if p.method == "GetPlayerFromCharacter" then
                    add(u(op.A + 2), "character", 88, "arg")
                elseif p.method == "Create" and base and base:match("TweenService$") then
                    add(u(op.A + 2), "instance", 62, "arg")
                    add(u(op.A + 3), "tweenInfo", 78, "arg")
                    add(u(op.A + 4), "properties", 72, "arg")
                elseif p.method == "Raycast" then
                    add(u(op.A + 2), "origin", 66, "arg")
                    add(u(op.A + 3), "direction", 72, "arg")
                    add(u(op.A + 4), "params", 58, "arg")
                elseif p.method == "AddTag" or p.method == "RemoveTag" or p.method == "HasTag" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "tag", 72, "arg")
                elseif p.method == "AddItem" then
                    add(u(op.A + 2), "instance", 56, "arg")
                    add(u(op.A + 3), "lifetime", 68, "arg")
                end
                local path
                if p.method == "GetService" and arg then
                    path = tostring(arg)
                elseif (p.method == "WaitForChild" or p.method == "FindFirstChild" or p.method == "FindFirstAncestor") and arg then
                    path = base and (base .. "." .. tostring(arg)) or tostring(arg)
                elseif (p.method == "FindFirstChildOfClass" or p.method == "FindFirstChildWhichIsA") and arg then
                    path = tostring(arg)
                else
                    path = base
                    if p.method then path = path and (path .. ":" .. p.method) or p.method end
                end
                callpath = path
                seto(out, path, "call")
                pend[op.A] = nil
            else
                local cal = u(op.A)
                local co = geto(cal)
                local arg
                if (op.B or 0) == 0 or op.B > 1 then arg = select(1, cv(ir, u(op.A + 1))) end
                local path = co and co.path or nil
                local h = rbx.fromCall(path, arg) or words.call(path) or "result"
                local first = {
                    pcall = "success", xpcall = "success", ["coroutine.resume"] = "success",
                    next = "key", ["string.find"] = "startPos", ["math.modf"] = "integer",
                    ["math.frexp"] = "mantissa",
                }
                h = first[path] or h
                if path == "require" then
                    local ao = geto(u(op.A + 1))
                    local tail = ao and ao.path and ao.path:match("([%a_][%w_]*)$")
                    if tail and tail ~= "Parent" then h = words.clean(tail) end
                end
                callpath = path
                add(out, h, path == "require" and 112 or 98, "call")
                add(cal, "fn", 48, "callee")
                seto(out, path, "call")
                if path == "table.insert" then
                    add(u(op.A + 1), "list", 52, "arg")
                    add(u(op.A + 2), "item", 46, "arg")
                elseif path == "pairs" or path == "ipairs" or path == "next" then
                    add(u(op.A + 1), "items", 44, "arg")
                elseif path == "pcall" or path == "xpcall" then
                    add(u(op.A + 1), "fn", 66, "arg")
                elseif path == "task.spawn" or path == "task.defer" or path == "task.delay" then
                    local r = path == "task.delay" and op.A + 2 or op.A + 1
                    add(u(r), "callback", 68, "arg")
                elseif path == "assert" then
                    add(u(op.A + 1), "condition", 48, "arg")
                end
            end
            if (op.C or 0) > 2 then
                local multi = {
                    pcall = { "success", "result" },
                    xpcall = { "success", "result" },
                    ["coroutine.resume"] = { "success", "result" },
                    next = { "key", "value" },
                    ["string.find"] = { "startPos", "endPos" },
                    ["math.modf"] = { "integer", "fraction" },
                    ["math.frexp"] = { "mantissa", "exponent" },
                }
                local set = multi[callpath]
                for r = op.A, op.A + op.C - 2 do
                    local i = r - op.A + 1
                    local h = set and set[i] or (i == 1 and nil or ("result" .. tostring(i)))
                    if h then add(d(r), h, set and 96 or 35, "multi") end
                end
            end
        elseif name == "NEWTABLE" or name == "DUPTABLE" then
            add(d(op.A), "data", 28, "table")
            seto(d(op.A), "data", "table")
        elseif name == "NEWCLOSURE" or name == "DUPCLOSURE" then
            local child = ir.proto.Protos and ir.proto.Protos[(op.D or 0) + 1]
            add(d(op.A), child and child.Name or "fn", 88, "closure")
        elseif name == "NOT" then
            local so = geto(u(op.B))
            if so then add(d(op.A), "not" .. ((words.call(so.path) or "value"):gsub("^%l", string.upper)), 52, "bool") end
        elseif name == "LENGTH" then
            local so = geto(u(op.B))
            if so then
                local x = words.call(so.path)
                if x then add(d(op.A), x .. "Count", 66, "len") else add(d(op.A), "count", 54, "len") end
            else
                add(d(op.A), "count", 48, "len")
            end
        elseif name == "FORGPREP" or name == "FORGPREP_NEXT" or name == "FORGPREP_INEXT" then
            local target = ins.jumpTarget(pc, op)
            local so = geto(u(op.A + 1)) or geto(u(op.A))
            prep[target] = so and (words.call(so.path) or words.field(so.path)) or nil
        elseif name == "FORGLOOP" then
            local nvar = math.max(1, bit32.band(op.AuxValue and op.AuxValue.Value or 0, 0xff))
            local src = prep[pc]
            for i = 1, nvar do
                local v = d(op.A + 2 + i)
                if i == 1 and nvar == 1 then add(v, words.iter(src), 86, "iter")
                elseif i == 1 then add(v, "key", 68, "iter")
                elseif i == 2 then add(v, words.iter(src) or "value", 82, "iter")
                else add(v, "value" .. tostring(i), 48, "iter") end
            end
        elseif name == "FORNLOOP" then
            add(d(op.A + 3), "i", 62, "numfor")
        end
    end

    for _, n in ipairs(ir.ops) do
        local op, pc, name = n.op, n.pc, n.name
        local uses = ir.ssa.usesByPC[pc] or {}
        local function u(r) return ir:resolve(uses[r]) end
        if name == "JUMPIF" or name == "JUMPIFNOT" then
            add(u(op.A), "enabled", 38, "condition")
        elseif name == "GETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "SETTABLE" then
            add(u(op.C), "key", 42, "index")
        elseif name == "CONCAT" then
            for r = op.B, op.C do add(u(r), "text", 30, "concat") end
        elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" then
            add(u(op.B), "num", 24, "math")
            add(u(op.C), "num", 24, "math")
        end
    end

    local best, score = {}, {}
    for v, set in pairs(hints) do
        for name, h in pairs(set) do
            local rank = h.score + math.min(20, math.max(0, (h.hits or 1) - 1) * 4)
            if not score[v] or rank > score[v] or (rank == score[v] and name < best[v]) then
                best[v], score[v] = name, rank
            end
        end
    end

    ir.hints = hints
    ir.bestname = best
    ir.namescore = score
    ir.origin = origin
    return ir
end

return pass