local pass = {}

function pass.run(ir)
    local changed = true
    while changed do
        changed = false
        for _, phis in pairs(ir.phis) do
            for _, p in pairs(phis) do
                if not ir.dead[p.id] and not p.missing then
                    local one
                    local many = false
                    for raw in pairs(p.inputs or {}) do
                        local id = ir:resolve(raw)
                        if id and id ~= p.id then
                            if one and one ~= id then many = true break end
                            one = id
                        end
                    end
                    if one and not many then
                        ir.alias[p.id] = one
                        ir.dead[p.id] = true
                        ir.vals[p.id].dead = true
                        changed = true
                    end
                end
            end
        end
    end
    ir:reindex()
    return ir
end

return pass
