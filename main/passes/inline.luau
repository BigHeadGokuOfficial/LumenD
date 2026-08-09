local ins = require("main.bytecode.instructions")

local pass = {}

local function quiet(ir, a, b)
    local pc = ins.next(ir.proto, a, ir.cfg.aux)
    while pc < b do
        local n = ir.bypc[pc]
        if n and not n.quiet then return false end
        pc = ins.next(ir.proto, pc, ir.cfg.aux)
    end
    return true
end

local function mutablevalues(ir, check)
    local mutable = {}
    local changed = true


    for id, objectset in pairs(ir.objectSets or {}) do
        if next(objectset) then
            local resolved = ir:resolve(id)
            if resolved then mutable[resolved] = true end
        end
    end

    for _, n in ipairs(ir.ops) do
        if n.name == "NEWTABLE" or n.name == "DUPTABLE" or n.name == "NEWCLASS" then
            local defs = ir.ssa.defsByPC[n.pc] or {}
            local v = ir:resolve(defs[n.op.A])
            if v then mutable[v] = true end
        end
    end

    while changed do
        if check then check() end
        changed = false
        for _, n in ipairs(ir.ops) do
            if n.name == "MOVE" then
                local uses = ir.ssa.usesByPC[n.pc] or {}
                local defs = ir.ssa.defsByPC[n.pc] or {}
                local src = ir:resolve(uses[n.op.B])
                local dst = ir:resolve(defs[n.op.A])
                if src and dst and mutable[src] and not mutable[dst] then mutable[dst] = true; changed = true end
            end
        end
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                local pid = ir:resolve(p.id)
                if pid and not mutable[pid] then
                    for raw in pairs(p.inputs or {}) do
                        local src = ir:resolve(raw)
                        if src and mutable[src] then mutable[pid] = true; changed = true break end
                    end
                end
            end
        end
    end
    return mutable
end

function pass.run(ir, check)
    local mutable = mutablevalues(ir, check)
    ir.mutableObjects = mutable

    for id, v in pairs(ir.vals) do
        if check then check() end
        id = ir:resolve(id)
        local protected = id and ir.outssa and ir.outssa.materialize and ir.outssa.materialize[id]
        if id and not ir.dead[id] and v.kind == "def" and not mutable[id] and not protected then
            local u = ir:only(id)
            local n = v.pc and ir.bypc[v.pc]
            if u and u.pc and n and ir.cfg.blockmap[v.pc] == ir.cfg.blockmap[u.pc] then
                local useop = ir.bypc[u.pc]
                if n.pure and (not useop or useop.name ~= "CAPTURE") then
                    ir.inline[id] = true
                elseif n.name == "CALL" or n.name == "CALLFB" then
                    local nx = ins.next(ir.proto, v.pc, ir.cfg.aux)
                    if u.pc == nx or quiet(ir, v.pc, u.pc) then ir.inline[id] = true end
                end
            end
        end
    end

    for id in pairs(ir.const) do
        id = ir:resolve(id)
        local protected = id and ir.outssa and ir.outssa.materialize and ir.outssa.materialize[id]
        if id and not mutable[id] and not protected then
            local ok = ir:count(id) > 0
            for _, u in ipairs(ir:uses(id) or {}) do
                local useop = u.pc and ir.bypc[u.pc] or nil
                if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
            end
            if ok then ir.inline[id] = true end
        end
    end
    return ir
end

return pass
