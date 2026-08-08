local id = require("main.naming.identifiers")

local dbg = {}

function dbg.ranges(proto)
    local out = {}
    if not (proto and proto.HasDebugInfo and proto.LocalVariables) then return out end

    for _, info in ipairs(proto.LocalVariables) do
        local reg = info.Register
        local name = id.clean(info.Name)
        if name then
            local list = out[reg] or {}
            out[reg] = list
            list[#list + 1] = {
                name = name,
                first = info.StartPc or 0,
                last = info.EndPc or math.huge,
            }
        end
    end

    for _, list in pairs(out) do
        table.sort(list, function(a, b)
            if a.first == b.first then return a.last < b.last end
            return a.first < b.first
        end)
    end

    return out
end

function dbg.at(ranges, reg, pc)
    local list = ranges[reg]
    if not list then return nil end
    local p = math.max(0, (pc or 1) - 1)
    local best
    for _, info in ipairs(list) do
        if p >= info.first and p < info.last then
            if not best or info.first >= best.first then best = info end
        end
    end
    return best
end

return dbg