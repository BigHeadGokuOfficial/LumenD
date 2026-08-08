local bc = {}

function bc.fromScript(obj)
    assert(typeof(obj) == "Instance", "LumenDecomp: target must be a Roblox Instance")
    assert(type(getscriptbytecode) == "function", "LumenDecomp: executor does not expose getscriptbytecode()")
    local ok, raw = pcall(getscriptbytecode, obj)
    if not ok then error("LumenDecomp: getscriptbytecode failed: " .. tostring(raw), 2) end
    local ty = typeof(raw)
    assert(type(raw) == "string" or ty == "buffer", "LumenDecomp: getscriptbytecode returned unsupported type " .. tostring(ty))
    if type(raw) == "string" then
        assert(#raw > 0, "LumenDecomp: getscriptbytecode returned empty bytecode")
    elseif ty == "buffer" then
        assert(buffer.len(raw) > 0, "LumenDecomp: getscriptbytecode returned empty bytecode")
    end
    return raw
end

function bc.try(obj)
    local ok, raw = pcall(bc.fromScript, obj)
    if ok then return true, raw end
    return false, tostring(raw)
end

return bc
