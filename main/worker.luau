local cfg = require("main.config")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:warm()
    local ok, err = iri.warm()
    if not ok then error(err, 2) end
    return true
end

function worker:decompileBytecode(raw, opt)
    opt = cfg(opt)
    local parsed = iri.get():Deserialize(raw, opt.iridium)
    local src = decomp.new(opt):decompileParsed(parsed)
    return src
end

return worker
