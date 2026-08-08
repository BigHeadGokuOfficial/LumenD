# LumenDecomp V4.0.0

```lua
local lumen = loadstring(game:HttpGet("https://raw.githubusercontent.com/Floorzey/LumenD/main/lumen.luau"))()
```

```lua
local options = lumen.DecompilerOptions.new()
options.SmartVariableRenamer = true
options.FunctionDeclarations = true
options.FidelityMode = true

print(lumen:decompile(script, options))
```

`main/` mirrors Lumen's original internal module layout and filenames. `lumen.luau` is the bundled build.

Credits: Moon / DexSerializer, ActualMasterOogway / Iridium.
