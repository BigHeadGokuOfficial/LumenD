local id = require("main.naming.identifiers")

local types = {}

local map = {
    boolean = "flag",
    number = "num",
    integer = "num",
    string = "text",
    table = "data",
    ["function"] = "fn",
    thread = "thread",
    vector = "vec",
    buffer = "buf",
    userdata = "obj",
}

function types.hint(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    return map[name] or id.lowerCamel(name:gsub("^userdata#", "obj"))
end

function types.text(info)
    if not info then return nil end
    local name = info.UserdataName or info.Name
    if not name then return nil end
    local safe = { boolean = true, number = true, string = true, buffer = true, integer = true, any = true }
    local out
    if info.UserdataName and id.valid(info.UserdataName) then out = info.UserdataName
    elseif safe[name] then out = name end
    if not out then return nil end
    if info.IsOptional and out ~= "any" then out = out .. "?" end
    return out
end

function types.ranges(proto)
    local out = {}
    for _, info in ipairs(proto and proto.LocalTypes or {}) do
        local reg = info.Register
        local list = out[reg] or {}
        out[reg] = list
        list[#list + 1] = info
    end
    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.StartPc == b.StartPc then return a.EndPc < b.EndPc end
            return a.StartPc < b.StartPc
        end)
    end
    return out
end

function types.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.StartPc and p < info.EndPc then
            if not best or info.StartPc >= best.StartPc then best = info end
        end
    end
    return best
end

function types.param(proto, reg)
    local fn = proto and proto.FunctionType
    local list = fn and fn.ParameterTypes
    return list and list[reg + 1] or nil
end

return types