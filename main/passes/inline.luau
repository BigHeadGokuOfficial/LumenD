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

function pass.run(ir)
    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and v.kind == "def" then
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
        local ok = ir:count(id) > 0
        for _, u in ipairs(ir:uses(id) or {}) do
            local useop = u.pc and ir.bypc[u.pc] or nil
            if u.phi or (useop and useop.name == "CAPTURE") then ok = false break end
        end
        if ok then ir.inline[id] = true end
    end
    return ir
end

return pass
