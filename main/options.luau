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
        NativeReadability = true,
        NativeUrl = "http://127.0.0.1:7331/decompile",
        NativeKey = 203,
        StructuredBudgetSeconds = 1.25,
        StructuredMaxInstructions = 32000,
        StructuredMaxProtoInstructions = 16000,
        StructuredMaxBlocks = 1024,
        formatter = {
            IndentWidth = 4,
            MaxLineLength = 110,
            TableInlineLimit = 4,
            BlankLinesBetweenFunctions = true,
            AppendSemicolons = false,
            ParenthesizeConditions = false,
        },
    }
end

return opt
