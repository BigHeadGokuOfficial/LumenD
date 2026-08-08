
local core = {}

local roots = {
    Chat = true,
    CoreGui = true,
    CorePackages = true,
    RobloxReplicatedStorage = true,
    CoreScriptSyncService = true,
}

local player = {
    PlayerModule = true,
    RbxCharacterSounds = true,
    ChatScript = true,
    BubbleChat = true,
    PlayerScriptsLoader = true,
}

function core.root(obj)
    return obj and (roots[obj.Name] == true or roots[obj.ClassName] == true) or false
end

function core.is(obj)
    local cur = obj
    while cur and cur ~= game do
        if core.root(cur) then return true end
        if player[cur.Name] then
            local p = cur.Parent
            if p and (p.Name == "PlayerScripts" or p.Name == "StarterPlayerScripts") then
                return true
            end
        end
        cur = cur.Parent
    end
    return false
end

return core
