local dex = require("main.serialization.dex_serializer")
local iri = require("main.runtime.iridium")
local st = require("main.runtime.status")

local save = {}

local ready = false
local fail = nil
local cache = nil

local function cached(scr)
    if not cache then return nil end
    local v = cache[scr]
    if type(v) == "string" then return true, v end
    if type(v) == "table" then
        if v.success and type(v.source) == "string" then return true, v.source end
        return false, v.error or "cached decompile failure"
    end
    return nil
end

local function start(lumen)
    if ready then return true end
    if fail then return false, fail end

    iri.get()

    dex.SetDecompiler(function(scr)
        local hit, src = cached(scr)
        if hit ~= nil then
            if hit then return src end
            return nil, tostring(src)
        end

        st.set("Decompiling", scr)
        local ok, out = pcall(function()
            return lumen:decompile(scr, { aggressive = false })
        end)

        if ok then return out end
        return nil, tostring(out)
    end)

    local ok, result, err = pcall(dex.Init)
    if not ok then
        fail = tostring(result)
        return false, fail
    end

    if result ~= true then
        fail = tostring(err or "DexSerializer.Init returned false")
        return false, fail
    end

    ready = true
    return true
end

function save.run(lumen, obj, file, opt)
    local ok, err = start(lumen)
    if not ok then
        error("LumenDecomp serializer init failed: " .. tostring(err), 2)
    end

    opt = opt or {}
    if opt.Decompile == nil then opt.Decompile = true end
    if opt.Binary == nil then opt.Binary = true end

    local old = cache
    cache = opt.SourceCache

    local pass = {}
    for k, v in pairs(opt) do
        if k ~= "SourceCache" then pass[k] = v end
    end

    local callok, a, b = pcall(dex.Save, obj, file, pass)
    cache = old

    if not callok then error(a, 2) end
    return a, b
end

function save.info()
    return {
        name = "DexSerializer",
        author = "Moon",
        blob = "60004ee8688b6c3a0b2b17bb246bb12928dd9079",
        embedded = true,
        ready = ready,
    }
end

return save
