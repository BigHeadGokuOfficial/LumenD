local env = require("main.runtime.environment")
local http = require("main.runtime.http")
local patch = require("main.runtime.iridium_patch")

local iri = {}

local owner = "ActualMasterOogway"
local repo = "Iridium"
local commit = "2a834af6c6f72918a9222eb4ac6b258e4c6cd4bf"
local rawBase = "https://raw.githubusercontent.com/" .. owner .. "/" .. repo .. "/" .. commit .. "/"

local cache = {}
local NIL = {}
local LOADING = {}
local root = nil

local function resolve(name)
    if name == "@root" then
        return "Src/init.luau"
    end

    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end

    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local req

req = function(name)
    local path = resolve(name)
    local hit = cache[path]

    if hit == LOADING then
        error("LumenDecomp: cyclic Iridium dependency at " .. path, 2)
    elseif hit ~= nil then
        return hit == NIL and nil or hit
    end

    cache[path] = LOADING

    local src = http.get(rawBase .. path)
    src = patch.apply(path, src)
    src = "local require = __LUMEN_IRIDIUM_REQUIRE\n" .. src

    local chunk, err = loadstring(src, "@Iridium/" .. path)
    if not chunk then
        cache[path] = nil
        error("LumenDecomp: failed compiling Iridium/" .. path .. ": " .. tostring(err), 2)
    end

    local ok, value = pcall(chunk)
    if not ok then
        cache[path] = nil
        error("LumenDecomp: failed loading Iridium/" .. path .. ": " .. tostring(value), 2)
    end

    cache[path] = value == nil and NIL or value
    return value
end

function iri.get()
    if root then
        return root
    end

    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local e = env.get()
    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)

    e[key] = req
    local ok, value = pcall(req, "@root")

    if old == nil then
        e[key] = nil
    else
        e[key] = old
    end

    if not ok then
        error(value, 2)
    end

    assert(type(value) == "table" and type(value.Deserialize) == "function",
        "LumenDecomp: Iridium root did not expose Deserialize")

    root = value
    return root
end

function iri.info()
    local pi = patch.info()
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
    }
end

return iri