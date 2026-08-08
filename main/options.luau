
local opt = {}

function opt.new()
    return {
        SmartVariableRenamer = true,
        FunctionDeclarations = true,
        GuardClauses = true,
        ConstantFolding = true,
        ConditionalStructurer = true,
        DoBlockInsertionThreshold = 0,
    }
end

return opt
