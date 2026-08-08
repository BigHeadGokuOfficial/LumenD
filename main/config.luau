local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = true,
    iridium = nil,
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[k] = v end end
    return out
end
