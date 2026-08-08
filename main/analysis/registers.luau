local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then
        set[value] = true
    end
end

local function range(set, first, last)
    for reg = first, last do
        add(set, reg)
    end
end

function regs.readWrite(op)
    local reads, writes = {}, {}
    local name = ins.name(op)
    local A, B, C = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL"
        or name == "GETIMPORT" or name == "NEWTABLE" or name == "DUPTABLE"
        or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, A)

    elseif name == "MOVE" then
        add(reads, B); add(writes, A)

    elseif name == "SETGLOBAL" or name == "SETUPVAL" then
        add(reads, A)

    elseif name == "GETTABLE" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "SETTABLE" then
        add(reads, A); add(reads, B); add(reads, C)

    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then
        add(reads, B); add(writes, A)

    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then
        add(reads, A); add(reads, B)

    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then
        add(reads, B); add(writes, A); add(writes, A + 1)

    elseif name == "CALL" or name == "CALLFB" then
        if B == 0 then add(reads, A) else range(reads, A, A + B - 1) end
        if C == 0 then add(writes, A) elseif C > 1 then range(writes, A, A + C - 2) end

    elseif name == "RETURN" then
        if B == 0 then add(reads, A) elseif B > 1 then range(reads, A, A + B - 2) end

    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV"
        or name == "MOD" or name == "POW" or name == "IDIV"
        or name == "AND" or name == "OR" then
        add(reads, B); add(reads, C); add(writes, A)

    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK"
        or name == "MODK" or name == "POWK" or name == "IDIVK"
        or name == "ANDK" or name == "ORK" then
        add(reads, B); add(writes, A)

    elseif name == "SUBRK" or name == "DIVRK" then
        add(reads, C); add(writes, A)

    elseif name == "CONCAT" then
        range(reads, B, C); add(writes, A)

    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then
        add(reads, B); add(writes, A)

    elseif name == "SETLIST" then
        add(reads, A)
        if C == 0 then add(reads, B) elseif C > 1 then range(reads, B, B + C - 2) end

    elseif name == "FORNPREP" or name == "FORNLOOP" then
        range(reads, A, A + 3); range(writes, A + 2, A + 3)

    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, A, A + 2)

    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, A, A + 2); add(writes, A + 2)
        if count > 0 then range(writes, A + 3, A + 2 + count) end

    elseif name == "GETVARARGS" then
        if B == 0 then add(writes, A) elseif B > 1 then range(writes, A, A + B - 2) end

    elseif name == "CAPTURE" then
        if A == 0 or A == 1 then add(reads, B) end

    elseif name == "JUMPIF" or name == "JUMPIFNOT"
        or name == "JUMPXEQKNIL" or name == "JUMPXEQKB"
        or name == "JUMPXEQKN" or name == "JUMPXEQKS"
        or name == "CMPPROTO" then
        add(reads, A)

    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ"
        or name == "JUMPIFLT" or name == "JUMPIFLE"
        or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, A); add(reads, bit32.band(aux, 0xff))

    elseif name == "NEWCLASSMEMBER" then
        add(reads, A); add(reads, C)

    elseif name == "NEWCLASS" then
        if B ~= 0xff then add(reads, B) end
        add(writes, A)
    end

    return reads, writes
end

function regs.stats(proto, aux, cache)
    local stats = {}
    aux = aux or ins.auxSlots(proto)

    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = {
                reads = 0, writes = 0,
                firstWrite = nil, lastWrite = nil,
                firstRead = nil, lastRead = nil,
                firstAccess = nil, lastAccess = nil,
            }
            stats[reg] = entry
        end
        return entry
    end

    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local op = proto.Instructions[pc]
            local pair = cache and cache[pc]
            local reads, writes
            if pair then
                reads, writes = pair.reads, pair.writes
            else
                reads, writes = regs.readWrite(op)
            end

            for reg in pairs(reads) do
                local entry = get(reg)
                entry.reads += 1
                entry.firstRead = entry.firstRead or pc
                entry.lastRead = pc
                entry.firstAccess = entry.firstAccess or pc
                entry.lastAccess = pc
            end

            local name = ins.name(op)
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local entry = get(reg)
                    entry.writes += 1
                    entry.firstWrite = entry.firstWrite or pc
                    entry.lastWrite = pc
                    entry.firstAccess = entry.firstAccess or pc
                    entry.lastAccess = pc
                end
            end
        end
    end

    return stats
end

return regs