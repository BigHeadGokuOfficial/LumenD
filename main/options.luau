
local opt = {}

function opt.new()
    return {
        SmartVariableRenamer = true,
        FunctionDeclarations = true,
        GuardClauses = true,
        ConstantFolding = true,
        ConditionalStructurer = true,
        DoBlockInsertionThreshold = 0,
        FidelityMode = true,
        StructuredBudgetSeconds = 1.25,
        StructuredMaxInstructions = 32000,
        StructuredMaxProtoInstructions = 16000,
        StructuredMaxBlocks = 1024,
    }
end

return opt
