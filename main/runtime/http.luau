local env = require("main.runtime.environment")

local http = {}

function http.get(url)
    local ok, body = pcall(function()
        return game:HttpGet(url)
    end)

    if ok and type(body) == "string" and #body > 0 then
        return body
    end

    local req = env.request()
    if type(req) == "function" then
        local rok, res = pcall(req, {
            Url = url,
            Method = "GET",
        })

        if rok and type(res) == "table" then
            local body = res.Body or res.body
            local code = res.StatusCode or res.Status or res.code

            if type(body) == "string"
                and #body > 0
                and (code == nil or (code >= 200 and code < 300)) then
                return body
            end
        end
    end

    error("LumenDecomp: HTTP GET failed for " .. tostring(url), 2)
end

return http
