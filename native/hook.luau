local http = game:GetService("HttpService")

local function env()
    if type(getgenv) == "function" then
        local ok, out = pcall(getgenv)

        if ok and type(out) == "table" then
            return out
        end
    end

    return _G
end

local function request()
    local e = env()
    local r = rawget(e, "request") or rawget(e, "http_request")

    if type(r) == "function" then
        return r
    end

    local s = rawget(e, "syn")

    if type(s) == "table" and type(s.request) == "function" then
        return s.request
    end
end

local function encode(raw)
    local e = env()
    local c = rawget(e, "crypt")

    if type(c) == "table" and type(c.base64) == "table" and type(c.base64.encode) == "function" then
        local ok, out = pcall(c.base64.encode, raw)

        if ok and type(out) == "string" then
            return out
        end
    end

    local f = rawget(e, "base64encode")

    if type(f) == "function" then
        local ok, out = pcall(f, raw)

        if ok and type(out) == "string" then
            return out
        end
    end
end

return function(api, opt)
    opt = type(opt) == "table" and opt or {}

    local old = api.decompileBytecode
    local url = opt.url or "http://127.0.0.1:7331/decompile"
    local key = tonumber(opt.key) or 203
    local dead = false

    function api:decompileBytecode(raw, cfg)
        if not dead then
            local req = request()
            local enc = encode(raw)

            if req and enc then
                local ok, res = pcall(req, {
                    Url = url,
                    Method = "POST",
                    Headers = {
                        ["Content-Type"] = "application/json",
                    },
                    Body = http:JSONEncode({
                        bytecode = enc,
                        key = key,
                    }),
                })

                if ok and type(res) == "table" then
                    local code = tonumber(res.StatusCode or res.Status or res.status)

                    if code == 200 and type(res.Body) == "string" then
                        local good, data = pcall(http.JSONDecode, http, res.Body)

                        if good and type(data) == "table" and data.success == true and type(data.source) == "string" then
                            return data.source, {
                                version = api.Version,
                                details = {
                                    status = "NATIVE",
                                    native = true,
                                    nativeBackend = data.backend or "medal",
                                    timings = {},
                                },
                            }
                        end
                    end
                else
                    dead = true
                end
            else
                dead = true
            end
        end

        return old(self, raw, cfg)
    end

    return api
end
