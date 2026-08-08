local pass = {}

function pass.run(ir)
    local memo = {}
    local function live(id, seen)
        id = ir:resolve(id)
        if not id then return false end
        if memo[id] ~= nil then return memo[id] end
        seen = seen or {}
        if seen[id] then return false end
        seen[id] = true
        for _, u in ipairs(ir:uses(id) or {}) do
            if u.pc then
                memo[id] = true
                seen[id] = nil
                return true
            elseif u.phi and live(u.phi, seen) then
                memo[id] = true
                seen[id] = nil
                return true
            end
        end
        seen[id] = nil
        memo[id] = false
        return false
    end

    for id, v in pairs(ir.vals) do
        id = ir:resolve(id)
        if id and not ir.dead[id] and not live(id) then
            local pc = v.pc
            local op = pc and ir.bypc[pc]
            if op and (op.drop or ir.const[id] ~= nil) then ir.dead[id] = true end
        end
    end
    return ir
end

return pass