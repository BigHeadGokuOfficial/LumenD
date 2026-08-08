local id = require("main.naming.identifiers")
local rbx = require("main.naming.roblox")
local dbg = require("main.naming.debug_names")
local ty = require("main.naming.types")

local names = {}
names.__index = names

function names.new(stats, opt, proto, debugranges, typeranges)
    return setmetatable({
        used = {},
        regs = {},
        locals = {},
        stats = stats or {},
        opt = opt or {},
        proto = proto,
        debug = debugranges or dbg.ranges(proto),
        typed = typeranges or ty.ranges(proto),
    }, names)
end

function names:unique(base)
    base = id.clean(base) or "value"
    if not self.used[base] then
        self.used[base] = true
        return base
    end
    local n = 2
    while self.used[base .. n] do n += 1 end
    local name = base .. n
    self.used[name] = true
    return name
end

function names:stable(reg)
    local stat = self.stats[reg]
    if not stat then return true end
    return (stat.writes or 0) <= 1 or self.opt.aggressive == true
end

function names:debugAt(reg, pc)
    return dbg.at(self.debug, reg, pc)
end

function names:typeAt(reg, pc)
    return ty.at(self.typed, reg, pc)
end

function names:isDebugAt(reg, pc)
    return self:debugAt(reg, pc) ~= nil
end

function names:nameAt(reg, pc, hint)
    local info = self:debugAt(reg, pc)
    if info then
        local key = "d:" .. tostring(reg) .. ":" .. tostring(info.first) .. ":" .. tostring(info.last) .. ":" .. info.name
        local old = self.locals[key]
        if old then return old end
        local name = self:unique(info.name)
        self.locals[key] = name
        return name
    end

    local typed = self:typeAt(reg, pc)
    if typed then
        local key = "t:" .. tostring(reg) .. ":" .. tostring(typed.StartPc) .. ":" .. tostring(typed.EndPc)
        local old = self.locals[key]
        if old then return old end
        local base = hint or ty.hint(typed)
        if base then
            local name = self:unique(base)
            self.locals[key] = name
            return name
        end
    end

    if not hint and pc == 1 then
        hint = ty.hint(ty.param(self.proto, reg))
        if not hint and reg < (self.proto.ParameterCount or 0) then hint = "arg" .. tostring(reg + 1) end
    end
    return self:name(reg, hint)
end

function names:name(reg, hint)
    local old = self.regs[reg]
    if old then return old end
    local base
    if hint and self:stable(reg) then base = id.clean(hint) end
    base = base or ("v" .. tostring(reg))
    local name = self:unique(base)
    self.regs[reg] = name
    return name
end

function names:reserve(name)
    name = id.clean(name)
    if name then self.used[name] = true end
    return name
end

function names:release(name)
    if name then self.used[name] = nil end
end

names.fromImport = rbx.fromImport
names.fromField = rbx.fromField
names.fromMethod = rbx.fromMethod
names.fromCall = rbx.fromCall

return names