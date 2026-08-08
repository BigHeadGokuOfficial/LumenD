local cfg = require("main.config")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")

local worker = {}

function worker:decompile(obj, opt)
    opt = cfg(opt)
    local raw = bc.fromScript(obj)
    local parsed = iri.get():Deserialize(raw, opt.iridium)
    local src = decomp.new(opt):decompileParsed(parsed)
    return src
end

return worker
