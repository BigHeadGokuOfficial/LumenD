local base = {
    aggressive = false,
    fold = true,
    inline = true,
    dce = true,
    conditions = true,
    guards = false,
    types = true,
    selects = true,
    returns = true,
    compound = true,
    inlineast = false,
    callbacks = false,
    booleans = true,
    smartnames = true,
    functions = true,
    doblocks = 0,
    iridium = nil,
    fidelity = true,
    native = true,
    nativeurl = "http://127.0.0.1:7331/decompile",
    nativekey = 203,
    structuredbudget = 1.25,
    structuredmaxinstructions = 32000,
    structuredmaxprotoinstructions = 16000,
    structuredmaxblocks = 1024,
    formatter = {
        IndentWidth = 4,
        MaxLineLength = 110,
        TableInlineLimit = 4,
        BlankLinesBetweenFunctions = true,
        AppendSemicolons = false,
        ParenthesizeConditions = false,
    },
}

local map = {
    SmartVariableRenamer = "smartnames",
    FunctionDeclarations = "functions",
    GuardClauses = "guards",
    ConstantFolding = "fold",
    ConditionalStructurer = "conditions",
    DoBlockInsertionThreshold = "doblocks",
    FidelityMode = "fidelity",
    NativeReadability = "native",
    NativeUrl = "nativeurl",
    NativeKey = "nativekey",
    StructuredBudgetSeconds = "structuredbudget",
    StructuredMaxInstructions = "structuredmaxinstructions",
    StructuredMaxProtoInstructions = "structuredmaxprotoinstructions",
    StructuredMaxBlocks = "structuredmaxblocks",
}

return function(opt)
    local out = {}

    for k, v in pairs(base) do
        if k == "formatter" and type(v) == "table" then
            local cpy = {}

            for a, b in pairs(v) do
                cpy[a] = b
            end

            out[k] = cpy
        else
            out[k] = v
        end
    end

    if opt then
        for k, v in pairs(opt) do
            local key = map[k] or k

            if key == "formatter" and type(v) == "table" then
                local mix = {}

                for a, b in pairs(out.formatter or {}) do
                    mix[a] = b
                end

                for a, b in pairs(v) do
                    mix[a] = b
                end

                out.formatter = mix
            else
                out[key] = v
            end
        end
    end

    out.doblocks = math.max(0, math.floor(tonumber(out.doblocks) or 0))
    out.nativekey = math.max(0, math.min(255, math.floor(tonumber(out.nativekey) or 203)))
    out.structuredbudget = math.max(0, tonumber(out.structuredbudget) or 1.25)
    out.structuredmaxinstructions = math.max(0, math.floor(tonumber(out.structuredmaxinstructions) or 32000))
    out.structuredmaxprotoinstructions = math.max(0, math.floor(tonumber(out.structuredmaxprotoinstructions) or 16000))
    out.structuredmaxblocks = math.max(0, math.floor(tonumber(out.structuredmaxblocks) or 1024))

    if type(out.nativeurl) ~= "string" or out.nativeurl == "" then
        out.nativeurl = base.nativeurl
    end

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
