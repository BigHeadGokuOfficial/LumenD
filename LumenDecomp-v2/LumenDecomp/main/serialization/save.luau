local dex = require("main.serialization.dex_serializer")
local iri = require("main.runtime.iridium")

local save = {}

local ready = false
local fail = nil

local function start(lumen)
    if ready then
        return true
    end

    if fail then
        return false, fail
    end

    iri.get()

    dex.SetDecompiler(function(scr)
        local ok, src = pcall(function()
            local out = lumen:decompile(scr, {
                aggressive = false,
            })
            return out
        end)

        if ok then
            return src
        end

        return nil, tostring(src)
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

    if opt.Decompile == nil then
        opt.Decompile = true
    end

    if opt.Binary == nil then
        opt.Binary = true
    end

    return dex.Save(obj, file, opt)
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
