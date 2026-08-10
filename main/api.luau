local ver = require("main.version")
local cfg = require("main.config")
local options = require("main.options")
local bc = require("main.runtime.bytecode")
local iri = require("main.runtime.iridium")
local decomp = require("main.decompiler.engine")
local dis = require("main.diagnostics.disassembler")
local view = require("main.diagnostics.inspect")
local env = require("main.runtime.environment")
local save = require("main.serialization.save")
local dump = require("main.dump")

local http = game:GetService("HttpService")
local state

local api = {
    Version = ver.version,
    Name = ver.name,
}

api.DecompilerOptions = { new = options.new }

local function parsebc(raw, opt)
    return iri.get():Deserialize(raw, opt.iridium)
end

local function request()
    local e = env.get()
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
    local e = env.get()
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

local function native(raw, opt)
    if opt.native == false or state == false then
        return nil
    end

    local req = request()
    local enc = encode(raw)

    if not req or not enc then
        state = false
        return nil
    end

    local body = http:JSONEncode({
        bytecode = enc,
        key = opt.nativekey,
    })

    local ok, res = pcall(req, {
        Url = opt.nativeurl,
        Method = "POST",
        Headers = {
            ["Content-Type"] = "application/json",
        },
        Body = body,
    })

    if not ok or type(res) ~= "table" then
        state = false
        return nil
    end

    local code = tonumber(res.StatusCode or res.Status or res.status)

    if code ~= 200 or type(res.Body) ~= "string" then
        return nil
    end

    local good, data = pcall(http.JSONDecode, http, res.Body)

    if not good or type(data) ~= "table" or data.success ~= true or type(data.source) ~= "string" then
        return nil
    end

    state = true

    return data.source, {
        version = ver.version,
        details = {
            status = "NATIVE",
            native = true,
            nativeBackend = data.backend or "medal",
            timings = {},
        },
    }
end

local function ping(opt)
    local req = request()

    if not req then
        return nil
    end

    local url = tostring(opt.nativeurl):gsub("/decompile/?$", "/health")
    local ok, res = pcall(req, {
        Url = url,
        Method = "GET",
    })

    if not ok or type(res) ~= "table" then
        return nil
    end

    local code = tonumber(res.StatusCode or res.Status or res.status)

    if code ~= 200 or type(res.Body) ~= "string" then
        return nil
    end

    local good, data = pcall(http.JSONDecode, http, res.Body)

    if good and type(data) == "table" and data.success == true then
        state = true
        return data
    end
end

function api:parseBytecode(raw, opt)
    return parsebc(raw, cfg(opt))
end

function api:parse(obj, opt)
    return self:parseBytecode(bc.fromScript(obj), opt)
end

function api:decompileBytecode(raw, opt)
    opt = cfg(opt)

    local src, meta = native(raw, opt)

    if src then
        return src, meta
    end

    local dt = os.clock()
    local parsed = parsebc(raw, opt)
    local decode = os.clock() - dt
    local d = decomp.new(opt)
    local source, details = d:decompileParsed(parsed)

    details.timings = details.timings or {}
    details.timings.decode = decode

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

function api:tryDecompileBytecode(raw, opt)
    local ok, source, metadata = pcall(function()
        local text, meta = self:decompileBytecode(raw, opt)
        return text, meta
    end)

    if ok then
        return {
            success = true,
            source = source,
            metadata = metadata,
        }
    end

    return {
        success = false,
        error = tostring(source),
    }
end

function api:tryDecompile(obj, opt)
    local ok, source, metadata = pcall(function()
        local text, meta = self:decompile(obj, opt)
        return text, meta
    end)

    if ok then
        return {
            success = true,
            source = source,
            metadata = metadata,
        }
    end

    return {
        success = false,
        error = tostring(source),
    }
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

function api:warm()
    local ok, err = iri.warm()

    if ok then
        return true
    end

    if ping(cfg()) then
        return true
    end

    error("LumenDecomp: Iridium warmup failed: " .. tostring(err), 2)
end

function api:nativeInfo(opt)
    return ping(cfg(opt))
end

function api:_iridiumPack()
    return iri.pack()
end

function api:dependencyInfo()
    return iri.info()
end

function api:save(obj, file, opt)
    return save.run(self, obj, file, opt)
end

function api:dump(opt)
    return dump.run(self, opt)
end

function api:auto(opt)
    return dump.auto(self, opt)
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
