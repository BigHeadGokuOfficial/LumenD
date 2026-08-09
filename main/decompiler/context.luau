
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
        tblobj = {},
        top = nil,
        bad = {},
        vnames = {},
        nexttmp = 0,
        symbolScopes = {},
        symbolUses = {},
        sequence = 0,
    }, ctx)

    for i = 1, #self.up do
        local name = self:upname(i)
        if name then naming:reserve(name) end
    end
    for r = 0, (proto.ParameterCount or 0) - 1 do
        local v = ir.ssa.params[r]
        local name = self:vname(v, r, nil, 1)
        self.declared[name] = 0
        local symbol = self.ir:nameid(v)
        if symbol then self.symbolScopes[symbol] = { depth = 0, seq = 0, name = name, parameter = true } end
    end
    return self
end

function ctx:updesc(index)
    return self.up[index]
end

local function semanticupname(ref, seen)
    if type(ref) == "string" then return ref end
    if type(ref) ~= "table" then return nil end
    if type(ref.name) == "string" and ref.name ~= "" then return ref.name end
    seen = seen or {}
    if seen[ref] then return nil end
    seen[ref] = true

    local name
    if ref.kind == "self" then
        name = ref.name
    elseif ref.kind == "upvalue" then
        name = semanticupname(ref.parent, seen)
    elseif ref.kind == "ref" then
        local owner = ref.owner
        name = owner and owner.v4 and owner.v4.cellNames and owner.v4.cellNames[ref.cell] or nil
    elseif ref.kind == "value" then
        name = ref.name
        if not name and ref.owner and ref.value then
            name = ref.owner:vname(ref.value, ref.reg, ref.debugname, ref.pc)
        end
    end
    if name and name ~= "" then ref.name = name end
    return name
end

function ctx:upname(index)
    local ref = self.up[index]
    if ref == nil then return nil end
    local name = semanticupname(ref)
    if not name or name == "" then
        error(("LumenV4: CAPTURE_VERIFY unresolved upvalue slot %d"):format(index), 2)
    end
    return name
end

local function semanticupcell(ref, seen)
    if type(ref) ~= "table" then return nil end
    if ref.cell then return ref.cell end
    seen = seen or {}
    if seen[ref] then return nil end
    seen[ref] = true
    if ref.kind == "upvalue" then return semanticupcell(ref.parent, seen) end
    return nil
end

function ctx:upcell(index)
    return semanticupcell(self.up[index])
end

function ctx:declaresymbol(symbol, name, depth)
    if symbol == nil then return end
    self.sequence += 1
    local nextscope = { depth = depth or self.indent, seq = self.sequence, name = name }
    local old = self.symbolScopes[symbol]
    if not old or nextscope.depth < old.depth or (nextscope.depth == old.depth and nextscope.seq < old.seq) then
        self.symbolScopes[symbol] = nextscope
    end
end

function ctx:usesymbol(symbol, name)
    if symbol == nil then return end
    self.sequence += 1
    local list = self.symbolUses[symbol]
    if not list then list = {}; self.symbolUses[symbol] = list end
    list[#list + 1] = { depth = self.indent, seq = self.sequence, name = name }
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

    if self.opt.smartnames == false then
        if di then
            name = self.naming:nameAt(r, pc, nil)
        elseif src and src.kind == "param" then
            name = self.naming:unique("arg" .. tostring(src.reg + 1))
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
    local v = self:veruse(pc, r)
    local symbol = v and self.ir:nameid(v) or ("r" .. tostring(r))
    local name = self:useName(pc, r, hint)
    if not self.alias[r] then self:usesymbol(symbol, name) end
    return ex.localref(symbol, name)
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
    if v and tab.get(self, v) then
        local node = self:usetbl(v, r, pc)
        if node then return node end
    end
    if v and self.ir.const[v] then return ex.literal(self.ir.const[v]) end
    if v and self.vals[v] then return self.vals[v] end
    return self:atom(r, hint, pc)
end

function ctx:use(pc, r, hint)
    return ex.str(self:usex(pc, r, hint))
end

function ctx:inline(pc, r, node)
    if self.v4 and self.v4.dispatcher then return false end
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
    local symbol = v and self.ir:nameid(v) or ("r" .. tostring(r))
    if fresh then
        self.declared[name] = self.indent
        self:declaresymbol(symbol, name, self.indent)
        local an = self:ann(r, pc)
        stmt = self.ast:add({ kind = "assign", names = { name }, symbols = { symbol }, values = { node }, declare = true, annotations = { an } })
    else
        stmt = self.ast:add({ kind = "assign", names = { name }, symbols = { symbol }, values = { node }, declare = false })
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
        local v = self:verdef(pc, r)
        local symbol = v and self.ir:nameid(v) or ("r" .. tostring(r))
        self:declaresymbol(symbol, name, self.indent)
        self.ast:add({ kind = "decl", names = { name }, symbols = { symbol }, annotations = { an } })
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
            local v = self:verdef(pc, regs[i]); self:declaresymbol(v and self.ir:nameid(v) or ("r" .. tostring(regs[i])), name, self.indent)
            local an = self:ann(regs[i], pc)
            typed[i] = name .. (an and (": " .. an) or "")
        end
        nodes[#nodes + 1] = self:out("local " .. table.concat(typed, ", ") .. " = " .. rhs)
    else
        if fresh > 0 then
            for i, name in ipairs(list) do
                local depth = self.declared[name]
                if depth == nil or depth > self.indent then
                    self.declared[name] = self.indent
                    local v = self:verdef(pc, regs[i]); self:declaresymbol(v and self.ir:nameid(v) or ("r" .. tostring(regs[i])), name, self.indent)
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
            self:declaresymbol(self.ir:nameid(item.p.id), name, self.indent)
            self:out("local " .. name)
        end
    end
end
function ctx:preparedispatch()
    if self.dispatchStorage then return end
    local storage = self.naming:unique("__slots")
    local cells = self.naming:unique("__cells")
    self.dispatchStorage = storage
    self.dispatchCells = cells
    self.declared[storage] = 0
    self.declared[cells] = 0
    self:out("local " .. storage .. " = {}")
    self:out("local " .. cells .. " = {}")

    local lexical = {}
    for _, raw in pairs(self.ssa.params or {}) do
        local id = self.ir:nameid(raw)
        if id then lexical[id] = true end
    end
    for _, n in ipairs(self.ir.ops or {}) do
        if n.name == "NEWCLOSURE" or n.name == "DUPCLOSURE" then
            local id = self.ir:def(n.pc, n.op.A)
            local fam = id and self.ir:nameid(id)
            if fam then lexical[fam] = true end
        end
    end

    self.dispatchLexical = lexical
    self.dispatchNames = {}
    self.dispatchPlainVname = self.basevname or self.vname
    for cid in pairs(self.ir.cells or {}) do
        self.v4.cellNames[cid] = cells .. "[" .. tostring(cid) .. "].v"
    end

    local oldvname = self.vname
    self.vname = function(ctxself, value, reg, hint, pc)
        local raw = value and ctxself.ir:resolve(value)
        local cid
        if pc and raw then
            local def = ctxself.ssa.defsByPC[pc] and ctxself.ssa.defsByPC[pc][reg]
            if def and ctxself.ir:resolve(def) == raw then cid = ctxself.ir.cellDef and ctxself.ir.cellDef[pc] and ctxself.ir.cellDef[pc][reg] end
            if not cid then
                local use = ctxself.ssa.usesByPC[pc] and ctxself.ssa.usesByPC[pc][reg]
                if use and ctxself.ir:resolve(use) == raw then cid = ctxself.ir.cellUse and ctxself.ir.cellUse[pc] and ctxself.ir.cellUse[pc][reg] end
            end
        end
        if cid then return cells .. "[" .. tostring(cid) .. "].v" end
        local id = value and ctxself.ir:nameid(value)
        if id and not lexical[id] then
            local name = ctxself.dispatchNames[id]
            if not name then
                name = storage .. "[" .. tostring(id) .. "]"
                ctxself.dispatchNames[id] = name
                ctxself.declared[name] = 0
                ctxself:declaresymbol(id, name, 0)
            end
            return name
        end
        local plain = ctxself.dispatchPlainVname
        if plain then return plain(ctxself, value, reg, hint, pc) end
        return oldvname(ctxself, value, reg, hint, pc)
    end
end

function ctx:dispatchbase(value, reg, pc)
    local id = value and self.ir:nameid(value)
    if id and self.dispatchLexical and not self.dispatchLexical[id] then
        local name = self.dispatchNames and self.dispatchNames[id]
        if not name then
            name = self.dispatchStorage .. "[" .. tostring(id) .. "]"
            self.dispatchNames[id] = name
            self.declared[name] = 0
            self:declaresymbol(id, name, 0)
        end
        return name
    end
    local base = self.dispatchPlainVname or self.basevname
    if base then return base(self, value, reg, nil, pc) end
    return self:vname(value, reg, nil, pc)
end

function ctx:closecells(pc)
    if not self.dispatchCells then return end
    local map = self.ir.cellCloseValue and self.ir.cellCloseValue[pc]
    if not map then return end
    local regs = {}
    for r in pairs(map) do regs[#regs + 1] = r end
    table.sort(regs)
    for _, r in ipairs(regs) do
        local rec = map[r]
        local value = rec and rec.value and self.ir:resolve(rec.value)
        if value then
            local base = self:dispatchbase(value, r, pc)
            local cids = {}; for cid in pairs(rec.cells or {}) do cids[#cids + 1] = cid end
            table.sort(cids)
            for _, cid in ipairs(cids) do
                local cell = self.dispatchCells .. "[" .. tostring(cid) .. "]"
                self:out("if " .. cell .. " ~= nil then " .. base .. " = " .. cell .. ".v; " .. cell .. " = nil end")
            end
        end
    end
end

function ctx:prepareoutssa()
    local outssa = self.ir.outssa
    if not outssa or not outssa.verified then
        error("LumenV4: SSA_DESTRUCT out-of-SSA verification did not complete", 2)
    end
    self.outssaNames = self.outssaNames or {}
    self.outssaEdges = self.outssaEdges or {}
    local nameset, names = {}, {}
    for pred, bysucc in pairs(outssa.edgeCopies or {}) do
        for succ, copies in pairs(bysucc) do
            for _, copy in ipairs(copies) do
                local block = self.cfg.blocks[succ]
                local name = self:vname(copy.dstValue, copy.reg, nil, block and block.startPC or 1)
                self.outssaNames[copy.dst] = name
                if not nameset[name] and self.declared[name] == nil then
                    nameset[name] = true
                    names[#names + 1] = name
                    self.declared[name] = 0
                    self:declaresymbol(copy.dst, name, 0)
                end
            end
        end
    end
    table.sort(names)
    for i = 1, #names, 12 do
        local part = {}
        for j = i, math.min(i + 11, #names) do part[#part + 1] = names[j] end
        self:out("local " .. table.concat(part, ", "))
    end
    self.v4.outssaVerified = true
    self.v4.outssaCopies = outssa.copyCount or 0
end

function ctx:hasedge(pred, succ)
    local outssa = self.ir.outssa
    local list = outssa and outssa.edgeCopies and outssa.edgeCopies[pred] and outssa.edgeCopies[pred][succ]
    return list ~= nil and #list > 0
end

function ctx:edge(pred, succ)
    if not pred or not succ or pred == succ then return end
    local outssa = self.ir.outssa
    local copies = outssa and outssa.edgeCopies and outssa.edgeCopies[pred] and outssa.edgeCopies[pred][succ]
    if not copies or #copies == 0 then return end

    self.outssaNames = self.outssaNames or {}
    self.outssaEdges = self.outssaEdges or {}
    local pending = {}
    local pb, sb = self.cfg.blocks[pred], self.cfg.blocks[succ]
    for _, copy in ipairs(copies) do
        local dst = self.outssaNames[copy.dst] or self:vname(copy.dstValue, copy.reg, nil, sb and sb.startPC or 1)
        self.outssaNames[copy.dst] = dst
        local src
        if copy.undef then
            src = "nil"
        else
            src = self.outssaNames[copy.src] or self:vname(copy.srcValue, copy.reg, nil, pb and pb.endPC or 1)
            self.outssaNames[copy.src] = src
        end
        if copy.src and not copy.undef then self:usesymbol(copy.src, src) end
        if dst ~= src then pending[#pending + 1] = { dst = dst, src = src, variable = copy.undef ~= true } end
    end

    local serial = 0
    while #pending > 0 do
        serial += 1
        if serial > #copies * 4 + 8 then error("LumenV4: SSA_DESTRUCT parallel copy resolution did not converge", 2) end
        local used = {}
        for _, copy in ipairs(pending) do if copy.variable then used[copy.src] = true end end
        local pick
        for i, copy in ipairs(pending) do
            if not used[copy.dst] then pick = i break end
        end
        if pick then
            local copy = table.remove(pending, pick)
            self:out(copy.dst .. " = " .. copy.src)
        else
            local first = pending[1]
            local tmp = self.naming:unique("phiTemp")
            self:out("local " .. tmp .. " = " .. first.dst)
            for _, copy in ipairs(pending) do
                if copy.variable and copy.src == first.dst then copy.src = tmp end
            end
        end
    end

    local key = tostring(pred) .. ">" .. tostring(succ)
    self.outssaEdges[key] = (self.outssaEdges[key] or 0) + 1
end

function ctx:edgepc(frompc, topc)
    local pred = frompc and self.cfg.blockmap[frompc]
    local succ = topc and self.cfg.blockmap[topc]
    if pred and succ then self:edge(pred, succ) end
end

function ctx:verifyoutssa()
    local outssa = self.ir.outssa
    if not outssa or not outssa.verified then return false, "analysis" end
    for pred, bysucc in pairs(outssa.edgeCopies or {}) do
        for succ, copies in pairs(bysucc) do
            if #copies > 0 then
                local key = tostring(pred) .. ">" .. tostring(succ)
                if not self.outssaEdges or not self.outssaEdges[key] then
                    return false, key
                end
            end
        end
    end
    return true
end

function ctx:verifyexpr()
    for _, node in pairs(self.expr or {}) do ex.verify(node) end
    for _, node in pairs(self.vals or {}) do ex.verify(node) end
    self.v4.exprVerified = true
    return true
end

function ctx:verifyscope()
    for symbol, uses in pairs(self.symbolUses or {}) do
        local decl = self.symbolScopes and self.symbolScopes[symbol]
        if not decl then
            error("LumenV4: SCOPE_VERIFY semantic symbol " .. tostring(symbol) .. " has no lexical declaration", 2)
        end
        for _, use in ipairs(uses) do
            if decl.depth > use.depth then
                error(("LumenV4: SCOPE_VERIFY symbol %s (%s) escapes declaration depth %d -> use depth %d"):format(tostring(symbol), tostring(use.name), decl.depth, use.depth), 2)
            end
            if decl.depth == use.depth and decl.seq > use.seq and not decl.parameter then
                error(("LumenV4: SCOPE_VERIFY symbol %s (%s) used before declaration"):format(tostring(symbol), tostring(use.name)), 2)
            end
        end
    end
    self.v4.scopeVerified = true
    return true
end


return ctx
