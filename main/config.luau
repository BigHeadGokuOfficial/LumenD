
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
    structuredbudget = 1.25,
    structuredmaxinstructions = 32000,
    structuredmaxprotoinstructions = 16000,
    structuredmaxblocks = 1024,
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
    FidelityMode = "fidelity",
    StructuredBudgetSeconds = "structuredbudget",
    StructuredMaxInstructions = "structuredmaxinstructions",
    StructuredMaxProtoInstructions = "structuredmaxprotoinstructions",
    StructuredMaxBlocks = "structuredmaxblocks",
}

return function(opt)
    local out = {}
    for k, v in pairs(base) do out[k] = v end
    if opt then for k, v in pairs(opt) do out[map[k] or k] = v end end
    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    out.structuredbudget = math.max(0, tonumber(out.structuredbudget) or 1.25)
    out.structuredmaxinstructions = math.max(0, math.floor(tonumber(out.structuredmaxinstructions) or 32000))
    out.structuredmaxprotoinstructions = math.max(0, math.floor(tonumber(out.structuredmaxprotoinstructions) or 16000))
    out.structuredmaxblocks = math.max(0, math.floor(tonumber(out.structuredmaxblocks) or 1024))
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
