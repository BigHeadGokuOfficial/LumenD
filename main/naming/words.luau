
local id = require("main.naming.identifiers")

local w = {}

local bad = {
    get = true, find = true, fetch = true, load = true, read = true, make = true,
    create = true, build = true, new = true, resolve = true, compute = true,
    calc = true, clone = true, wait = true, require = true,
}

local keep = {
    is = true, has = true, can = true, should = true, did = true, was = true,
}

local function tail(s)
    if type(s) ~= "string" then return nil end
    return s:match("([%a_][%w_]*)$")
end

function w.clean(s)
    if type(s) ~= "string" then return nil end
    s = s:gsub("^_+", ""):gsub("_+$", "")
    if s == "" then return nil end
    return id.clean(id.lowerCamel(s))
end

function w.singular(s)
    s = w.clean(s)
    if not s then return nil end
    local low = s:lower()
    if low:match("ies$") and #s > 4 then return s:sub(1, -4) .. "y" end
    if low:match("sses$") or low:match("shes$") or low:match("ches$") or low:match("xes$") or low:match("zes$") then
        return s:sub(1, -3)
    end
    if low:sub(-1) == "s" and low:sub(-2) ~= "ss" and #s > 3 then return s:sub(1, -2) end
    return s
end

function w.call(s)
    s = tail(s)
    if not s then return nil end
    local lc = id.lowerCamel(s)
    for pre in pairs(bad) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then
            local c = lc:sub(n + 1, n + 1)
            if c:match("[A-Z]") or s:sub(n + 1, n + 1):match("[A-Z]") then
                return w.clean(s:sub(n + 1))
            end
        end
    end
    for pre in pairs(keep) do
        local n = #pre
        if lc:sub(1, n):lower() == pre and #lc > n then return w.clean(s) end
    end
    return w.clean(s)
end

function w.method(s)
    if type(s) ~= "string" then return nil end
    if s == "Connect" then return "connection" end
    if s == "Clone" then return "clone" end
    if s == "GetChildren" then return "children" end
    if s == "GetDescendants" then return "descendants" end
    if s == "GetAttributes" then return "attributes" end
    if s == "GetAttribute" then return "attribute" end
    if s == "GetPropertyChangedSignal" then return "signal" end
    return w.call(s)
end

function w.field(s)
    return w.clean(s)
end

function w.iter(s)
    local x = w.singular(s)
    if not x or x == s and (s == "data" or s == "list" or s == "array" or s == "items") then return "item" end
    return x or "item"
end

return w
