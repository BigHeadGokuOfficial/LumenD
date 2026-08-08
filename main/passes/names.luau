
local pass = {}

function pass.run(ir)
    local parent = {}

    local function root(x)
        x = ir:resolve(x)
        if not x then return nil end
        local p = parent[x]
        if not p then parent[x] = x return x end
        if p ~= x then parent[x] = root(p) end
        return parent[x]
    end

    local function join(a, b)
        a, b = root(a), root(b)
        if a and b and a ~= b then parent[b] = a end
    end

    for id in pairs(ir.vals) do parent[id] = id end

    for _, phis in pairs(ir.phis) do
        for _, p in pairs(phis) do
            local pid = ir:resolve(p.id)
            if pid and not ir.dead[pid] and ir:count(pid) > 0 then
                for raw in pairs(p.inputs or {}) do join(pid, raw) end
            end
        end
    end

    local fam = {}
    for id in pairs(ir.vals) do fam[id] = root(id) end
    ir.family = fam
    return ir
end

return pass
