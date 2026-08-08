local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = true,
    types = true,
    selects = true,
    returns = true,
    compound = true,
    inlineast = true,
    callbacks = true,
    booleans = true,
    smartnames = true,
    functions = true,
    doblocks = 0,
    iridium = nil,
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then
        for k, v in pairs(opt) do out[map[k] or k] = v end
    end
    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    return out
end
