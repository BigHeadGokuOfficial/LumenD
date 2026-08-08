local id = require("main.naming.identifiers")

local rbx = {}

local fields = {
    LocalPlayer = "localPlayer",
    Character = "character",
    Humanoid = "humanoid",
    HumanoidRootPart = "rootPart",
    PrimaryPart = "primaryPart",
    CurrentCamera = "camera",
    PlayerGui = "playerGui",
    Backpack = "backpack",
    PlayerScripts = "playerScripts",
    Mouse = "mouse",
}

function rbx.fromImport(path)
    if type(path) ~= "string" then return nil end
    local tail = path:match("([A-Za-z_][A-Za-z0-9_]*)$")
    if not tail then return nil end

    if path:match("^game%.") or path == tail then
        return id.clean(tail)
    end

    return id.lowerCamel(tail)
end

function rbx.fromField(field)
    return fields[field] or id.lowerCamel(field)
end

function rbx.fromMethod(method, arg)
    if method == "GetService" and arg then
        return id.clean(arg)
    elseif (method == "WaitForChild" or method == "FindFirstChild") and arg then
        return id.lowerCamel(arg)
    elseif method == "FindFirstChildOfClass" and arg then
        return id.lowerCamel(arg)
    elseif method == "GetPlayerFromCharacter" then
        return "player"
    elseif method == "Clone" then
        return "clone"
    elseif method == "Connect" then
        return "connection"
    end
end

function rbx.fromCall(callee, arg)
    if callee == "Instance.new" and arg then
        return id.lowerCamel(arg)
    elseif callee == "require" then
        return "module"
    end
end

return rbx
