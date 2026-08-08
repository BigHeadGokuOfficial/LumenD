# LumenDecomp V3.1

```lua
Binary = true
Decompile = true
Tree = true

local lumen = loadstring(game:HttpGet("https://raw.githubusercontent.com/BigHeadGokuOfficial/LumenD/main/LumenDecomp/lumen.luau"))()
```

That starts the accessible-game dump automatically.

- `Binary` writes `FullGame.rbxl`.
- `Decompile` reconstructs accessible scripts.
- `Tree` mirrors script paths into `.luau` files.
- A top-screen status bar shows the current script and full Roblox path.
- Output is written under `LumenDecomp/<PlaceId>/dump_<timestamp>/` in the executor workspace.

Only instances and bytecode replicated/accesssible to the client can be dumped.

Credits: Moon / DexSerializer, ActualMasterOogway / Iridium.
