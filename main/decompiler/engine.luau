local irbuild = require("main.ir.build")
local irpass = require("main.passes.pipeline")
local names = require("main.naming.resolver")
local lower = require("main.ast.lower")
local astpass = require("main.ast.pipeline")
local printer = require("main.ast.printer")
local context = require("main.decompiler.context")
local ops = require("main.decompiler.ops")
local cond = require("main.recover.conditions")
local branch = require("main.recover.branches")
local loops = require("main.recover.loops")
local ins = require("main.bytecode.instructions")
local ex = require("main.output.expr")

local decomp = {}
decomp.__index = decomp

local function loopused(st, r, a, b)
    local pc = a
    while pc < b do
        local uses = st.ssa.usesByPC[pc]
        if uses and uses[r] then return true end
        pc = st:next(pc)
    end
    return false
end

function decomp.new(opt)
    return setmetatable({ opt = opt or {} }, decomp)
end

function decomp:_state(proto, up, ph)
    local ir = irbuild.run(proto)
    ir.paramhints = ph or {}
    ir = irpass.run(ir, self.opt)
    local naming = names.new(ir.cfg.registerStats, self.opt, proto)
    return context.new(proto, ir, naming, up, lower.new(), self.opt)
end

function decomp:_child(proto, up, ph)
    local st = self:_state(proto, up, ph)
    local args = {}
    for i = 0, (proto.ParameterCount or 0) - 1 do
        local name = st:vname(st.ssa.params[i], i, nil, 1)
        local an = st:paramann(i)
        args[#args + 1] = name .. (an and (": " .. an) or "")
    end
    if proto.IsVararg then args[#args + 1] = "..." end
    self:_region(st, 1, #proto.Instructions + 1, {})
    local root = astpass.run(st.ast:done(), self.opt)
    return root, st, args
end

function decomp:_numfor(st, pc, op, stop, active)
    local info = loops.numInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local a = op.A
    local old = st.alias[a + 3]
    local lv = st:verdef(loop, a + 3)
    local depth = (active.loopdepth or 0) + 1
    local fall = ({ "i", "j", "k", "n" })[depth] or ("i" .. tostring(depth))
    local var = not loopused(st, a + 3, st:next(pc), loop) and "_" or st:vname(lv, a + 3, fall, loop)
    local limit = ex.str(st:loopx(pc, loop, a))
    local step = ex.str(st:loopx(pc, loop, a + 1))
    local init = ex.str(st:loopx(pc, loop, a + 2))
    local head = "for " .. var .. " = " .. init .. ", " .. limit
    if step ~= "1" then head = head .. ", " .. step end
    st:out(head .. " do")
    st.indent += 1
    st.alias[a + 3] = var
    st.declared[var] = st.indent
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    st.alias[a + 3] = old
    return info.exit
end

function decomp:_genfor(st, pc, op, stop, active)
    local info = loops.genInfo(st, pc, op, stop)
    if not info then return nil end
    local loop = info.loop
    local lop = info.op
    local aux = lop.AuxValue and lop.AuxValue.Value or 0
    local n = math.max(1, bit32.band(aux, 0xff))
    local depth = (active.loopdepth or 0) + 1
    local vars, old = {}, {}
    for i = 1, n do
        local r = op.A + 2 + i
        old[r] = st.alias[r]
        local hint = i == 1 and (n == 1 and "item" or "key") or (i == 2 and "value" or ("value" .. tostring(i)))
        local v = st:verdef(loop, r)
        vars[i] = not loopused(st, r, st:next(pc), loop) and "_" or st:vname(v, r, hint, loop)
    end

    local src
    local regs = { op.A, op.A + 1, op.A + 2 }
    local gv = st:veruse(pc, op.A)
    local g = gv and st.group[gv]
    if g and st:hidegroup(g, pc, loop, regs) then
        src = ex.str(g.node)
    elseif ins.name(op) == "FORGPREP_INEXT" then
        src = "ipairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    elseif ins.name(op) == "FORGPREP_NEXT" then
        src = "pairs(" .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ")"
    else
        src = ex.str(st:loopx(pc, loop, op.A)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 1)) .. ", " .. ex.str(st:loopx(pc, loop, op.A + 2))
    end

    st:out("for " .. table.concat(vars, ", ") .. " in " .. src .. " do")
    st.indent += 1
    for i = 1, n do
        local r = op.A + 2 + i
        st.alias[r] = vars[i]
        st.declared[vars[i]] = st.indent
    end
    local prev = active.loop
    local olddepth = active.loopdepth
    active.loop = { breakpc = info.exit, contpc = loop }
    active.loopdepth = depth
    self:_region(st, st:next(pc), loop, active)
    active.loop = prev
    active.loopdepth = olddepth
    st:trim(st.indent)
    st.indent -= 1
    st:out("end")
    for i = 1, n do st.alias[op.A + 2 + i] = old[op.A + 2 + i] end
    return info.exit
end

function decomp:_emitif(st, info, active, word)
    st:out((word or "if") .. " " .. ex.str(info.cond) .. " then")
    st.indent += 1
    local old = active.join
    active.join = info.join
    self:_region(st, info.a, info.b, active)
    active.join = old
    st:trim(st.indent)
    st.indent -= 1

    if info.c then
        local sub = branch.elseifInfo(st, info.c, info.join)
        if sub then
            self:_emitif(st, sub, active, "elseif")
            return
        end
        st:out("else")
        st.indent += 1
        old = active.join
        active.join = info.join
        self:_region(st, info.c, info.d, active)
        active.join = old
        st:trim(st.indent)
        st.indent -= 1
    end
    st:out("end")
end

function decomp:_region(st, start, stop, active)
    local pc = start
    active = active or {}

    while pc < stop and pc <= #st.proto.Instructions do
        if st.cfg.aux[pc] or st.consumed[pc] then
            pc += 1
        else
            local rep
            if not active["repeat:" .. tostring(pc)] then rep = loops.repeatInfo(st, pc) end
            if rep and rep.latch < stop then
                active["repeat:" .. tostring(pc)] = true
                st:out("repeat")
                st.indent += 1
                local prev = active.loop
                active.loop = { breakpc = rep.exit, contpc = rep.cont }
                self:_region(st, rep.body, rep.latch, active)
                active.loop = prev
                local x = cond.fall(st, rep.latch, st.proto.Instructions[rep.latch])
                st:trim(st.indent)
                st.indent -= 1
                st:out("until " .. ex.str(x))
                active["repeat:" .. tostring(pc)] = nil
                pc = rep.exit
            else
                local forever = loops.foreverInfo(st, pc, stop)
                if forever then
                    st:out("while true do")
                    st.indent += 1
                    local prev = active.loop
                    active.loop = { breakpc = forever.exit, contpc = forever.cont, cont2 = forever.latch }
                    self:_region(st, forever.body, forever.latch, active)
                    active.loop = prev
                    st:trim(st.indent)
                    st.indent -= 1
                    st:out("end")
                    pc = forever.exit
                else
                    local op = st.proto.Instructions[pc]
                    local name = ins.name(op)

                    if name == "FORNPREP" then
                        pc = self:_numfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
                        pc = self:_genfor(st, pc, op, stop, active) or ops.run(self, st, pc)
                    elseif name == "CMPPROTO" then
                        local target = ins.jumpTarget(pc, op)
                        local join = st:join(pc)
                        if join and target > pc and target < join and join <= stop then
                            self:_region(st, target, join, active)
                            pc = join
                        else
                            st:badpc(pc, "unrecognized CMPPROTO inline guard -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    elseif ins.isConditional(op) and name ~= "FORNLOOP" and name ~= "FORGLOOP" then
                        local loop = active.loop
                        local target = ins.jumpTarget(pc, op)
                        if loop and target == loop.breakpc then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then break end")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("if " .. ex.str(cond.jump(st, pc, op)) .. " then continue end")
                            pc = st:next(pc)
                        else
                            local bp = cond.bool(st, pc, op)
                            if bp then
                                pc = bp
                            else
                                local wh = loops.whileInfo(st, pc)
                                if wh and wh.exit <= stop then
                                    st:hoist(pc)
                                    st:out("while " .. ex.str(wh.cond) .. " do")
                                    st.indent += 1
                                    local prev = active.loop
                                    active.loop = { breakpc = wh.exit, contpc = wh.cont }
                                    self:_region(st, wh.body, wh.bodyend, active)
                                    active.loop = prev
                                    st:trim(st.indent)
                                    st.indent -= 1
                                    st:out("end")
                                    pc = wh.exit
                                else
                                    local info = branch.info(st, pc, stop)
                                    if info and info.join <= stop then
                                        st:hoist(info.join)
                                        self:_emitif(st, info, active)
                                        pc = info.join
                                    else
                                        st:badpc(pc, "unstructured conditional " .. name .. " -> " .. tostring(target))
                                        pc = st:next(pc)
                                    end
                                end
                            end
                        end
                    elseif name == "JUMP" or name == "JUMPBACK" or name == "JUMPX" then
                        local target = ins.jumpTarget(pc, op)
                        local loop = active.loop
                        if loop and target == loop.breakpc then
                            st:out("break")
                            pc = st:next(pc)
                        elseif loop and (target == loop.contpc or target == loop.cont2) then
                            st:out("continue")
                            pc = st:next(pc)
                        elseif target == stop or target == active.join then
                            pc = stop
                        else
                            st:badpc(pc, "unstructured jump -> " .. tostring(target))
                            pc = st:next(pc)
                        end
                    else
                        pc = ops.run(self, st, pc)
                    end
                end
            end
        end
    end
    return pc
end

function decomp:decompileProto(proto, up)
    local root, st = self:_child(proto, up or {})
    return printer.run(root), {
        cfg = st.cfg,
        ir = st.ir,
        ssa = st.ssa,
        ssaSummary = st.ssa:summary(),
        issues = st.bad,
    }
end

function decomp:decompileParsed(parsed)
    local proto = parsed.Protos[parsed.ProtoEntryPoint]
    assert(proto, "LumenDecomp: parsed bytecode has no entry proto")
    self.parsed = parsed
    local src, info = self:decompileProto(proto, {})
    self.parsed = nil
    return src, info
end

return decomp