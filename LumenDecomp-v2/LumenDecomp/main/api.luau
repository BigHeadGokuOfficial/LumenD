local ver = require("main.version")
local cfg = require("main.config")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")
local dis = require("main.diagnostics.disassembler")
local view = require("main.diagnostics.inspect")
local env = require("main.runtime.environment")
local save = require("main.serialization.save")

local api = {
    Version = ver.version,
    Name = ver.name,
}

local function parsebc(raw, opt)
    return iri.get():Deserialize(raw, opt.iridium)
end

function api:parseBytecode(raw, opt)
    return parsebc(raw, cfg(opt))
end

function api:parse(obj, opt)
    return self:parseBytecode(bc.fromScript(obj), opt)
end

function api:decompileBytecode(raw, opt)
    opt = cfg(opt)

    local parsed = parsebc(raw, opt)
    local d = decomp.new(opt)
    local source, details = d:decompileParsed(parsed)

    return source, {
        version = ver.version,
        bytecodeVersion = parsed.BytecodeVersion,
        typesVersion = parsed.TypesVersion,
        protoCount = parsed.ProtoCount,
        hasRobloxEnvelope = parsed.HasRobloxEnvelope,
        robloxTrailerVersion = parsed.RobloxTrailerVersion,
        details = details,
    }
end

function api:decompile(obj, opt)
    return self:decompileBytecode(bc.fromScript(obj), opt)
end

function api:tryDecompile(obj, opt)
    local ok, source, metadata = pcall(function()
        local text, meta = self:decompile(obj, opt)
        return text, meta
    end)

    if ok then
        return { success = true, source = source, metadata = metadata }
    end

    return { success = false, error = tostring(source) }
end

function api:disassemble(obj, opt)
    local parsed = self:parse(obj, opt)
    local proto = assert(parsed.Protos[parsed.ProtoEntryPoint])
    return dis.proto(proto), parsed
end

function api:inspectGraph(obj, opt)
    return view.graph(self:parse(obj, opt))
end

function api:inspectSSA(obj, opt)
    return view.ssa(self:parse(obj, opt))
end

function api:inspectIR(obj, opt)
    opt = cfg(opt)
    return view.ir(self:parse(obj, opt), opt)
end

function api:dependencyInfo()
    return iri.info()
end

function api:save(obj, file, opt)
    return save.run(self, obj, file, opt)
end

function api:serializerInfo()
    return save.info()
end

function api:installGlobal(name)
    name = name or "lumendecompile"
    local e = env.get()

    e[name] = function(obj, opt)
        local source = self:decompile(obj, opt)
        return source
    end

    return name
end

function api:installAsDecompiler()
    local e = env.get()
    local previous = rawget(e, "decompile")

    e.decompile = function(obj, opt)
        local source = self:decompile(obj, opt)
        return source
    end

    return previous
end

return api
