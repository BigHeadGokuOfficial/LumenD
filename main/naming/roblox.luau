
local id = require("main.naming.identifiers")
local words = require("main.naming.words")

local rbx = {}

local fields = {
    LocalPlayer = "localPlayer", Character = "character", Humanoid = "humanoid",
    HumanoidRootPart = "rootPart", PrimaryPart = "primaryPart", CurrentCamera = "camera",
    PlayerGui = "playerGui", Backpack = "backpack", PlayerScripts = "playerScripts",
    Mouse = "mouse", Parent = "parent", Position = "position", CFrame = "cframe",
    Size = "size", Name = "name", Value = "value", Enabled = "enabled",
    Visible = "visible", Health = "health", MaxHealth = "maxHealth", Team = "team",
    UserId = "userId", CharacterAdded = "characterAdded", OnClientEvent = "event",
    OnServerEvent = "event", Touched = "touched", AbsolutePosition = "position",
    AbsoluteSize = "size", AssemblyLinearVelocity = "velocity", AssemblyAngularVelocity = "angularVelocity",
}

function rbx.fromImport(path)
    if type(path) ~= "string" then return nil end
    local tail = path:match("([A-Za-z_][A-Za-z0-9_]*)$")
    if not tail then return nil end
    if path:match("^game%.") or path == tail then return id.clean(tail) end
    return id.lowerCamel(tail)
end

function rbx.fromField(field)
    return fields[field] or id.lowerCamel(field)
end

function rbx.fromMethod(method, arg)
    if method == "GetService" and arg then return id.lowerCamel(arg) end
    if method == "WaitForChild" or method == "FindFirstChild" or method == "FindFirstAncestor" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "child"
    end
    if method == "FindFirstChildOfClass" or method == "FindFirstChildWhichIsA" or method == "FindFirstAncestorOfClass" or method == "FindFirstAncestorWhichIsA" then
        return arg and (fields[arg] or id.lowerCamel(arg)) or "instance"
    end
    if method == "IsA" then
        if arg then return "is" .. arg:gsub("^%l", string.upper) end
        return "isType"
    end
    if method == "GetPlayerFromCharacter" then return "player" end
    if method == "GetPlayers" then return "playerList" end
    if method == "GetChildren" then return "children" end
    if method == "GetDescendants" then return "descendants" end
    if method == "GetMouse" then return "mouse" end
    if method == "GetPivot" then return "pivot" end
    if method == "GetAttribute" then return arg and id.lowerCamel(arg) or "attribute" end
    if method == "GetAttributes" then return "attributes" end
    if method == "GetPropertyChangedSignal" then return "signal" end
    if method == "Clone" then return "clone" end
    if method == "Connect" or method == "ConnectParallel" then return "connection" end
    if method == "Raycast" then return "raycastResult" end
    if method == "GetPartsInPart" or method == "GetPartBoundsInBox" or method == "GetPartBoundsInRadius" then return "parts" end
    if method == "JSONDecode" then return "data" end
    if method == "JSONEncode" then return "json" end
    if method == "GenerateGUID" then return "guid" end
    if method == "InvokeServer" or method == "Invoke" then return "result" end
    return words.method(method)
end

function rbx.fromCall(callee, arg)
    if callee == "Instance.new" and arg then return id.lowerCamel(arg) end
    local ctor = {
        ["Vector3.new"] = "vector", ["Vector2.new"] = "vector", ["CFrame.new"] = "cframe",
        ["CFrame.lookAt"] = "cframe", ["Color3.new"] = "color", ["Color3.fromRGB"] = "color",
        ["Color3.fromHSV"] = "color", ["UDim.new"] = "udim", ["UDim2.new"] = "udim2",
        ["UDim2.fromScale"] = "udim2", ["UDim2.fromOffset"] = "udim2",
        ["TweenInfo.new"] = "tweenInfo", ["RaycastParams.new"] = "raycastParams",
        ["OverlapParams.new"] = "overlapParams", ["Random.new"] = "random",
        ["NumberRange.new"] = "range", ["NumberSequence.new"] = "sequence",
        ["ColorSequence.new"] = "colorSequence", ["Region3.new"] = "region",
        ["Rect.new"] = "rect",
    }
    if ctor[callee] then return ctor[callee] end
    if callee == "require" then return "module" end
    if callee == "tonumber" then return "num" end
    if callee == "tostring" then return "text" end
    if callee == "typeof" or callee == "type" then return "typeName" end
    if callee == "table.clone" then return "copy" end
    if callee == "table.pack" then return "values" end
    if callee == "string.split" then return "parts" end
    if callee == "task.spawn" or callee == "task.defer" then return "thread" end
    return words.call(callee)
end

return rbx
