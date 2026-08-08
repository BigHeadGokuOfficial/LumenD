# This is currently not in polished state and I would not use it if I were you

# LumenDecomp V3.3.0

```lua
local g = getgenv()

g.Binary = true
g.Decompile = true
g.Tree = true
g.IgnoreCoreScripts = true
g.Parallel = true
g.MaxWorkers = 4

g.DecompilerOptions = {
    SmartVariableRenamer = true,
    FunctionDeclarations = true,
    GuardClauses = true,
    ConstantFolding = true,
    ConditionalStructurer = true,
    DoBlockInsertionThreshold = 0,
}

local lumen = loadstring(game:HttpGet("https://raw.githubusercontent.com/Floorzey/LumenD/main/lumen.luau"))()
```

```lua
local options = lumen.DecompilerOptions.new()
options.SmartVariableRenamer = true
options.FunctionDeclarations = true
options.GuardClauses = true
options.ConstantFolding = true
options.ConditionalStructurer = true
options.DoBlockInsertionThreshold = 0

print(lumen:decompile(script, options))
```

`DoBlockInsertionThreshold = 0` disables scope-block insertion. Set it above zero when generating very large source that needs tighter local-variable scopes for recompilation.

# Credits:

Moon / DexSerializer,

ActualMasterOogway / Iridium.
