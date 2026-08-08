
local patch = {}

local rev = "v13-3"

local function rep(s, a, b, tag)
    local p = s:find(a, 1, true)
    if not p then error("LumenDecomp: Iridium patch mismatch: " .. tag, 3) end
    return s:sub(1, p - 1) .. b .. s:sub(p + #a)
end

function patch.apply(path, src)
    src = src:gsub("\r\n", "\n"):gsub("\r", "\n")
    if path == "Src/Luau/Spec.luau" then
        src = rep(src, "LBC_VERSION_MAX = 11", "LBC_VERSION_MAX = 13", "spec.max")
        src = rep(src, "LBC_VERSION_TARGET = 6", "LBC_VERSION_TARGET = 9", "spec.target")
        src = rep(src, "    LBC_VERSION_TARGET = 9,\n", "    LBC_VERSION_TARGET = 9,\n    LBC_VERSION_CLASSES = 100,\n", "spec.classes")
        src = rep(src, "    LBC_CONSTANT_CLASS_SHAPE = 10,\n", "    LBC_CONSTANT_CLASS_SHAPE = 10,\n    LBC_CONSTANT_VECTORD = 11,\n", "spec.vectord")
        src = rep(src, [[    LOP__COUNT = { Index = 88, Name = "_COUNT", HasAux = false },]], [[    LOP_CMPPROTO = { Index = 88, Name = "CMPPROTO", HasAux = true },
    LOP_NEWCLASS = { Index = 89, Name = "NEWCLASS", HasAux = true },
    LOP__COUNT = { Index = 90, Name = "_COUNT", HasAux = false },]], "spec.v12ops")
        return src
    end

    if path == "Src/init.luau" then
        src = rep(src, [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX}, got {self.BytecodeVersion})`)
    end]], [[    if self.BytecodeVersion < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (self.BytecodeVersion > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and self.BytecodeVersion ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
        error(`Invalid bytecode version (expected {LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN}-{LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX} or classes, got {self.BytecodeVersion})`)
    end]], "init.classes")

        src = rep(src, [[    for i = 1, self.ProtoCount do
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
    end]], [[    self.ProtoSizes = {}
    for i = 1, self.ProtoCount do
        local ProtoSize = nil
        local ProtoStart = nil
        if self.BytecodeVersion >= 12 then
            ProtoSize = Bytecode:ReadVarInt()
            ProtoStart = Bytecode.Offset
            self.ProtoSizes[i] = ProtoSize
        end
        self.Protos[i] = Proto.new(Bytecode, self, Config.EncodingKey)
        if ProtoSize then
            local ProtoEnd = ProtoStart + ProtoSize
            if Bytecode.Offset < ProtoEnd then
                Bytecode:seek(ProtoEnd - Bytecode.Offset)
            elseif Bytecode.Offset > ProtoEnd then
                error(`Proto {i} overread ({Bytecode.Offset - ProtoEnd} bytes)`)
            end
        end
    end]], "init.sizes")

        src = rep(src, [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], [[local function SkipProto(Bytecode: Buffer.BufferReader, Version: number)
    if Version >= 12 then
        local ProtoSize = Bytecode:ReadVarInt()
        Bytecode:seek(ProtoSize)
        return
    end

    Bytecode:seek(4)

    if Version >= 4 then
        Bytecode:seek(1)
        Bytecode:seek(Bytecode:ReadVarInt())
    end]], "init.skiphead")

        src = rep(src, [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        end]], [[        elseif Kind == 10 then
            Bytecode:ReadVarInt()

            local Members = Bytecode:ReadVarInt() + Bytecode:ReadVarInt()

            for _ = 1, Members do
                Bytecode:ReadVarInt()
            end
        elseif Kind == 11 then
            Bytecode:seek(32)
        end]], "init.vectord")



        src = rep(src, [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX then
            return nil
        end]], [[        if Version < LuauSpec.LuauBytecodeTag.LBC_VERSION_MIN or (Version > LuauSpec.LuauBytecodeTag.LBC_VERSION_MAX and Version ~= LuauSpec.LuauBytecodeTag.LBC_VERSION_CLASSES) then
            return nil
        end]], "init.probeclasses")

        src = rep(src, [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        Bytecode:seek(4)]], [[        Bytecode:seek(Starts[MainId + 1] - Bytecode.Offset)

        if Version >= 12 then
            Bytecode:ReadVarInt()
        end

        Bytecode:seek(4)]], "init.probe")
        return src
    end

    if path == "Src/Classes/Proto.luau" then
        src = rep(src, [[        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], [[        elseif ConstantType == LuauSpec.LuauBytecodeConstants.LBC_CONSTANT_VECTORD then
            local x, y, z, w =
                Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64(), Bytecode:readf64()
            self.Constants[ConstantIndex] = Vector.new(x, y, z, w)
        else
            error(`Unexpected constant kind ({ConstantType})`)
        end]], "proto.vectord")

        local cost = [[    if Deserializer.BytecodeVersion >= 12 and bit32.band(self.Flags or 0, 8) ~= 0 then
        self.Cost = Bytecode:ReadVarInt64()
    end
]]
        local mark = "\n\treturn self\nend\n\nexport type Proto"
        local pos = src:find(mark, 1, true)
        if not pos then
            mark = "\n    return self\nend\n\nexport type Proto"
            pos = src:find(mark, 1, true)
        end
        if not pos then error("LumenDecomp: Iridium patch mismatch: proto.cost", 3) end
        src = src:sub(1, pos) .. cost .. src:sub(pos + 1)
        return src
    end

    return src
end

function patch.info()
    return { rev = rev, max = 13, target = 9, classes = 100 }
end

return patch
