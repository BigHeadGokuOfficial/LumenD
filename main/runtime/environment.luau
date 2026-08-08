
local env = {}

function env.get()
    if type(getgenv) == "function" then
        local ok, e = pcall(getgenv)
        if ok and type(e) == "table" then
            return e
        end
    end

    if type(getfenv) == "function" then
        local ok, e = pcall(getfenv, 0)
        if ok and type(e) == "table" then
            return e
        end
    end

    return _G
end

function env.request()
    local e = env.get()

    return rawget(e, "request")
        or rawget(e, "http_request")
        or (type(syn) == "table" and syn.request)
end

return env
