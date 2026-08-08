local env = require("main.runtime.environment")
local http = require("main.runtime.http")
local patch = require("main.runtime.iridium_patch")

local iri = {}

local owner = "ActualMasterOogway"
local repo = "Iridium"
local commit = "2a834af6c6f72918a9222eb4ac6b258e4c6cd4bf"
local rawBase = "https://raw.githubusercontent.com/" .. owner .. "/" .. repo .. "/" .. commit .. "/"

local paths = {
    "Src/init.luau",
    "Src/Deserializer.d.luau",
    "Src/Utilities/Buffer.luau",
    "Src/Luau/Spec.luau",
    "Src/Luau/TypeInfo.luau",
    "Src/Classes/Proto.luau",
    "Src/Classes/Instructions.luau",
    "Src/Classes/Instruction.luau",
    "Src/Classes/Hexadecimal.luau",
    "Src/Classes/Upvalue.luau",
    "Src/Classes/Constants/Nil.luau",
    "Src/Classes/Constants/Boolean.luau",
    "Src/Classes/Constants/Number.luau",
    "Src/Classes/Constants/String.luau",
    "Src/Classes/Constants/Import.luau",
    "Src/Classes/Constants/Table.luau",
    "Src/Classes/Constants/Closure.luau",
    "Src/Classes/Constants/Vector.luau",
    "Src/Classes/Constants/TableWithConstants.luau",
    "Src/Classes/Constants/Integer.luau",
    "Src/Classes/Constants/ClassShape.luau",
}

local cache = {}
local srcs = {}
local NIL = {}
local LOADING = {}
local root = nil
local loading = false
local loaderr = nil
local warming = false
local warmed = false
local warmerr = nil

local e = env.get()
local vend = rawget(e, "__LUMEN_IRIDIUM_VENDOR")
if type(vend) == "table" then
    for k, v in pairs(vend) do
        if type(k) == "string" and type(v) == "string" then srcs[k] = v end
    end
end

local function resolve(name)
    if name == "@root" then return "Src/init.luau" end
    local prefix = "@root/"
    if name:sub(1, #prefix) == prefix then
        return "Src/" .. name:sub(#prefix + 1) .. ".luau"
    end
    error("LumenDecomp: unsupported Iridium module " .. tostring(name), 3)
end

local function fetch(path)
    local src = srcs[path]
    if src then return src end
    src = http.get(rawBase .. path)
    srcs[path] = src
    return src
end

function iri.prefetch()
    if warmed then return true end
    if warming then
        while warming do task.wait() end
        if warmerr then return false, warmerr end
        return true
    end

    warming = true
    warmerr = nil
    local left = 0
    local errs = {}

    for _, path in ipairs(paths) do
        if not srcs[path] then
            left += 1
            task.spawn(function()
                local ok, val = pcall(http.get, rawBase .. path)
                if ok and type(val) == "string" and val ~= "" then
                    srcs[path] = val
                else
                    errs[#errs + 1] = path .. ": " .. tostring(val)
                end
                left -= 1
            end)
        end
    end

    while left > 0 do task.wait() end
    warming = false
    if #errs > 0 then
        warmerr = table.concat(errs, " | ")
        return false, warmerr
    end
    warmed = true
    return true
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
    local ok, value = pcall(function()
        local src = patch.apply(path, fetch(path))
        src = "local require = __LUMEN_IRIDIUM_REQUIRE\n" .. src
        local chunk, err = loadstring(src, "@Iridium/" .. path)
        if not chunk then
            error("LumenDecomp: failed compiling Iridium/" .. path .. ": " .. tostring(err), 0)
        end
        return chunk()
    end)

    if not ok then
        cache[path] = nil
        error("LumenDecomp: failed loading Iridium/" .. path .. ": " .. tostring(value), 2)
    end

    cache[path] = value == nil and NIL or value
    return value
end

function iri.get()
    if root then return root end
    if loading then
        while loading do task.wait() end
        if root then return root end
        error(loaderr or "LumenDecomp: Iridium load failed", 2)
    end

    loading = true
    loaderr = nil
    assert(type(loadstring) == "function", "LumenDecomp requires executor loadstring()")
    assert(type(buffer) == "table", "LumenDecomp requires Luau buffer support")

    local key = "__LUMEN_IRIDIUM_REQUIRE"
    local old = rawget(e, key)
    e[key] = req
    local ok, value = pcall(req, "@root")
    if old == nil then e[key] = nil else e[key] = old end

    if not ok then
        loading = false
        loaderr = tostring(value)
        error(value, 2)
    end

    if type(value) ~= "table" or type(value.Deserialize) ~= "function" then
        loading = false
        loaderr = "LumenDecomp: Iridium root did not expose Deserialize"
        error(loaderr, 2)
    end

    root = value
    loading = false
    return root
end

function iri.warm()
    iri.prefetch()
    local rok, val = pcall(iri.get)
    if not rok then return false, tostring(val) end
    return true
end

local function lit(s)
    for n = 3, 12 do
        local eq = string.rep("=", n)
        local close = "]" .. eq .. "]"
        if not s:find(close, 1, true) then
            return "[" .. eq .. "[" .. s .. close
        end
    end
    return string.format("%q", s)
end

function iri.pack()
    iri.prefetch()
    for _, path in ipairs(paths) do
        if not srcs[path] then
            local ok, val = pcall(fetch, path)
            if not ok then return nil, tostring(val) end
        end
    end
    local out = { "return {" }
    for _, path in ipairs(paths) do
        out[#out + 1] = "[" .. string.format("%q", path) .. "]=" .. lit(srcs[path]) .. ","
    end
    out[#out + 1] = "}"
    return table.concat(out)
end

function iri.info()
    local pi = patch.info()
    local n = 0
    for _ in pairs(srcs) do n += 1 end
    return {
        owner = owner,
        repo = repo,
        commit = commit,
        patch = pi.rev,
        patchedMax = pi.max,
        target = pi.target,
        classes = pi.classes,
        loaded = root ~= nil,
        prefetched = n,
        vendor = type(vend) == "table",
    }
end

return iri
