
local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = false,
    types = true,
    selects = false,
    returns = false,
    compound = false,
    inlineast = false,
    callbacks = false,
    booleans = false,
    smartnames = true,
    functions = true,
    doblocks = 0,
    iridium = nil,
    fidelity = true,
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
    FidelityMode = "fidelity",
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[map[k] or k] = v end end
    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    if out.fidelity ~= false then

        out.fold = false
        out.guards = false
        out.selects = false
        out.returns = false
        out.compound = false
        out.inlineast = false
        out.callbacks = false
        out.booleans = false
        out.doblocks = 0
    end
    return out
end
