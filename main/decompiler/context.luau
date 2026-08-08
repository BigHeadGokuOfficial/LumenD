local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")
local lit = require("main.output.literals")
local tab = require("main.recover.tables")
local ty = require("main.naming.types")

local ctx = {}
ctx.__index = ctx

function ctx.new(proto, ir, naming, up, ast, opt)
    local self = setmetatable({
        proto = proto,
        ir = ir,
        cfg = ir.cfg,
        ssa = ir.ssa,
        naming = naming,
        up = up or {},
        ast = ast,
        opt = opt or {},
        indent = 0,
        declared = {},
        namecall = {},
        consumed = {},
        alias = {},
        str = {},
        vals = {},
        expr = {},
        emit = {},
        group = {},
        tbl = {},
        top = nil,
        bad = {},
        vnames = {},
        nexttmp = 0,
    }, ctx)

    for _, name in ipairs(self.up) do naming:reserve(name) end
    for r = 0, (proto.ParameterCount or 0) - 1 do
        local v = ir.ssa.params[r]
        local name = self:vname(v, r, nil, 1)
        self.declared[name] = 0
    end
    return self
end

function ctx:out(s)
    return self.ast:emit(s)
end

function ctx:trim(depth)
    for name, d in pairs(self.declared) do
        if d >= depth then self.declared[name] = nil end
    end
end

function ctx:ann(r, pc)
    if self.opt.types == false then return nil end
    return ty.text(self.naming:typeAt(r, pc))
end

function ctx:paramann(r)
    if self.opt.types == false then return nil end
    return ty.text(ty.param(self.proto, r))
end

function ctx:badpc(pc, msg)
    local text = "pc " .. tostring(pc) .. ": " .. msg
    self.bad[#self.bad + 1] = text
    self:out("--[[ lumen: " .. text:gsub("%]%]", "] ]") .. " ]]")
end

function ctx:quiet(a, b)
    local pc = self:next(a)
    while pc < b do
        local n = self.ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = self:next(pc)
    end
    return true
end

function ctx:vname(v, r, hint, pc)
    local raw = self.ir:resolve(v)
    v = self.ir:nameid(raw)
    if not v then return self.naming:nameAt(r, pc or 1, hint) end
    local old = self.vnames[v]
    if old then return old end

    local di = pc and self.naming:debugAt(r, pc) or nil
    local ti = pc and self.naming:typeAt(r, pc) or nil
    local src = raw and self.ir.vals[raw] or nil
    local best = self.ir.bestname and self.ir.bestname[v] or nil
    local score = self.ir.namescore and self.ir.namescore[v] or 0
    local name

    if di then
        name = self.naming:nameAt(r, pc, nil)
    elseif best and score >= 80 then
        name = self.naming:unique(best)
    elseif ti then
        name = self.naming:nameAt(r, pc, hint or best)
    elseif best and score >= 55 then
        name = self.naming:unique(best)
    elseif src and src.kind == "param" then
        name = self.naming:unique(hint or (score >= 55 and best or nil) or ("arg" .. tostring(src.reg + 1)))
    elseif hint then
        name = self.naming:unique(hint)
    elseif best then
        name = self.naming:unique(best)
    else
        repeat
            name = "v" .. tostring(self.nexttmp)
            self.nexttmp += 1
        until not self.naming.used[name]
        name = self.naming:unique(name)
    end

    self.vnames[v] = name
    return name
end

function ctx:useName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:veruse(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:defName(pc, r, hint)
    if self.alias[r] then return self.alias[r] end
    local v = self:verdef(pc, r)
    return self:vname(v, r, hint, pc)
end

function ctx:reg(r, hint, pc)
    if self.alias[r] then return self.alias[r] end
    if pc then
        local u = self:veruse(pc, r)
        if u then return self:vname(u, r, hint, pc) end
        local d = self:verdef(pc, r)
        if d then return self:vname(d, r, hint, pc) end
    end
    return self.naming:name(r, hint)
end

function ctx:atom(r, hint, pc)
    return ex.atom(self:useName(pc, r, hint), false)
end

function ctx:veruse(pc, r)
    return self.ir:use(pc, r)
end

function ctx:verdef(pc, r)
    return self.ir:def(pc, r)
end

function ctx:tblmut(use, r)
    return tab.mut(self, use, r)
end

function ctx:usetbl(v, r, pc)
    return tab.use(self, v, r, pc)
end

function ctx:usex(pc, r, hint)
    local v = self:veruse(pc, r)
    if v and self.tbl[v] then
        local node = self:usetbl(v, r, pc)
        if node then return node end
    end
    if v and self.ir.const[v] then return ex.atom(self.ir.const[v], true) end
    if v and self.vals[v] then return self.vals[v] end
    return self:atom(r, hint, pc)
end

function ctx:use(pc, r, hint)
    return ex.str(self:usex(pc, r, hint))
end

function ctx:inline(pc, r, node)
    if self.naming:isDebugAt(r, pc) then return false end
    local v = self:verdef(pc, r)
    if not v or not self.ir.inline[v] then return false end
    if self.ir.const[v] then return true end
    local u = self.ir:only(v)
    if not u or not u.pc then return false end
    if node.stable then return true end
    local defop = self.ir.bypc[pc]
    local useop = self.ir.bypc[u.pc]
    if defop and useop and (defop.name == "GETGLOBAL" or defop.name == "GETIMPORT")
        and (useop.name == "CALL" or useop.name == "CALLFB") and useop.op.A == r then
        return true
    end
    if u.pc == self:next(pc) then return true end
    return self:quiet(pc, u.pc)
end

function ctx:set(pc, r, node, hint, raw)
    local v = self:verdef(pc, r)
    if v then self.expr[v] = node end
    if v and self.ir.dead[v] then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end
    if v and self:inline(pc, r, node) then
        self.vals[v] = node
        if raw ~= nil then self.str[v] = raw end
        return nil
    end

    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    local fresh = depth == nil or depth > self.indent
    local stmt
    if fresh then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        stmt = self:out("local " .. name .. (an and (": " .. an) or "") .. " = " .. ex.str(node))
    else
        stmt = self:out(name .. " = " .. ex.str(node))
    end
    if v then
        self.emit[v] = { node = stmt, name = name, fresh = fresh, depth = self.indent }
        if raw ~= nil then self.str[v] = raw end
    end
    return name
end

function ctx:decl(r, hint, pc)
    local name = self:defName(pc, r, hint)
    local depth = self.declared[name]
    if depth == nil or depth > self.indent then
        self.declared[name] = self.indent
        local an = self:ann(r, pc)
        self:out("local " .. name .. (an and (": " .. an) or ""))
    end
    return name
end

function ctx:multi(pc, regs, rhs, hints, node)
    local list = {}
    local fresh = 0
    local new = {}
    local nodes = {}
    for i, r in ipairs(regs) do
        local name = self:defName(pc, r, hints and hints[i] or nil)
        list[i] = name
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            fresh += 1
            new[#new + 1] = name
        end
    end
    if fresh == #list then
        local typed = {}
        for i, name in ipairs(list) do
            self.declared[name] = self.indent
            local an = self:ann(regs[i], pc)
            typed[i] = name .. (an and (": " .. an) or "")
        end
        nodes[#nodes + 1] = self:out("local " .. table.concat(typed, ", ") .. " = " .. rhs)
    else
        if fresh > 0 then
            for _, name in ipairs(list) do
                local depth = self.declared[name]
                if depth == nil or depth > self.indent then
                    self.declared[name] = self.indent
                    nodes[#nodes + 1] = self:out("local " .. name)
                end
            end
        end
        nodes[#nodes + 1] = self:out(table.concat(list, ", ") .. " = " .. rhs)
    end
    if node then
        local g = { nodes = nodes, new = new, depth = self.indent, node = node }
        for _, r in ipairs(regs) do
            local v = self:verdef(pc, r)
            if v then self.group[v] = g end
        end
    end
    return list
end

function ctx:only(v, a, b, r)
    if not v then return false end
    local block = self.cfg.blockmap[b]
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then
            if u.pc ~= a and u.pc ~= b then return false end
        elseif u.phi then
            local pv = self.ir.vals[self.ir:resolve(u.phi)]
            if not pv or pv.block ~= block or pv.reg ~= r then return false end
        else
            return false
        end
    end
    return true
end

function ctx:hide(v)
    local e = v and self.emit[v]
    if not e or not e.fresh or not e.node then return false end
    e.node.dead = true
    if self.declared[e.name] == e.depth then self.declared[e.name] = nil end
    self.naming:release(e.name)
    return true
end

function ctx:loopx(pc, loop, r)
    local v = self:veruse(pc, r)
    local node = v and self.expr[v]
    if not node or not node.stable or not self:only(v, pc, loop, r) then
        return self:usex(pc, r)
    end
    if self:hide(v) then return node end
    return self:usex(pc, r)
end

function ctx:hidegroup(g, pc, loop, regs)
    if not g or not g.nodes then return false end
    for _, r in ipairs(regs) do
        local v = self:veruse(pc, r)
        if not v or self.group[v] ~= g or not self:only(v, pc, loop, r) then return false end
    end
    for _, node in ipairs(g.nodes) do if node then node.dead = true end end
    for _, name in ipairs(g.new) do
        if self.declared[name] == g.depth then self.declared[name] = nil end
        self.naming:release(name)
    end
    return true
end

function ctx:raw(pc, r)
    local v = self:veruse(pc, r)
    return v and self.str[v] or nil
end

function ctx:next(pc)
    return ins.next(self.proto, pc, self.cfg.aux)
end

function ctx:join(pc)
    local bid = self.cfg.blockmap[pc]
    local id = bid and self.cfg.ipdom[bid]
    local b = id and self.cfg.blocks[id]
    return b and b.startPC or nil
end

function ctx:phlive(v, seen)
    v = self.ir:resolve(v)
    seen = seen or {}
    if not v or seen[v] then return false end
    seen[v] = true
    for _, u in ipairs(self.ir:uses(v) or {}) do
        if u.pc then return true end
        if u.phi and self:phlive(u.phi, seen) then return true end
    end
    return false
end

function ctx:hoist(pc)
    local bid = self.cfg.blockmap[pc]
    local phis = bid and self.ir.phis[bid]
    if not phis then return end
    local list = {}
    for r, p in pairs(phis) do
        local id = self.ir:resolve(p.id)
        if id == p.id and not self.ir.dead[id] and self:phlive(id) then list[#list + 1] = { r = r, p = p } end
    end
    table.sort(list, function(a, b) return a.r < b.r end)
    for _, item in ipairs(list) do
        local name = self:vname(item.p.id, item.r, nil, pc)
        local depth = self.declared[name]
        if depth == nil or depth > self.indent then
            self.declared[name] = self.indent
            self:out("local " .. name)
        end
    end
end

return ctx
