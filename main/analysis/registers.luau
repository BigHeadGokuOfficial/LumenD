local ins = require("main.bytecode.instructions")

local regs = {}

local function add(set, value)
    if type(value) == "number" and value >= 0 and value < 255 then set[value] = true end
end
local function range(set, first, last)
    for reg = first, math.min(last, 254) do add(set, reg) end
end


function regs.readWrite(op)
    local reads, writes, pack = {}, {}, {}
    local name = ins.name(op)
    local ra, rb, rc = op.A or 0, op.B or 0, op.C or 0
    local aux = op.AuxValue and op.AuxValue.Value or 0

    if name == "LOADNIL" or name == "LOADB" or name == "LOADN" or name == "LOADK"
        or name == "LOADKX" or name == "GETGLOBAL" or name == "GETUPVAL" or name == "GETIMPORT"
        or name == "NEWTABLE" or name == "DUPTABLE" or name == "NEWCLOSURE" or name == "DUPCLOSURE" then
        add(writes, ra)
    elseif name == "MOVE" then add(reads, rb); add(writes, ra)
    elseif name == "SETGLOBAL" or name == "SETUPVAL" then add(reads, ra)
    elseif name == "GETTABLE" then add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "SETTABLE" then add(reads, ra); add(reads, rb); add(reads, rc)
    elseif name == "GETTABLEKS" or name == "GETTABLEN" or name == "GETUDATAKS" then add(reads, rb); add(writes, ra)
    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then add(reads, ra); add(reads, rb)
    elseif name == "NAMECALL" or name == "NAMECALLUDATA" then add(reads, rb); add(writes, ra); add(writes, ra + 1)
    elseif name == "CALL" or name == "CALLFB" then
        add(reads, ra)
        if rb == 0 then
            pack.openReadFrom = ra + 1
            pack.consumesTop = true
        elseif rb > 1 then range(reads, ra + 1, ra + rb - 1) end
        if rc == 0 then
            add(writes, ra)
            pack.openWriteFrom = ra
            pack.producesTop = true
        elseif rc > 1 then range(writes, ra, ra + rc - 2) end
    elseif name == "RETURN" then
        if rb == 0 then add(reads, ra); pack.openReadFrom = ra; pack.consumesTop = true
        elseif rb > 1 then range(reads, ra, ra + rb - 2) end
    elseif name == "ADD" or name == "SUB" or name == "MUL" or name == "DIV" or name == "MOD" or name == "POW" or name == "IDIV" or name == "AND" or name == "OR" then
        add(reads, rb); add(reads, rc); add(writes, ra)
    elseif name == "ADDK" or name == "SUBK" or name == "MULK" or name == "DIVK" or name == "MODK" or name == "POWK" or name == "IDIVK" or name == "ANDK" or name == "ORK" then
        add(reads, rb); add(writes, ra)
    elseif name == "SUBRK" or name == "DIVRK" then add(reads, rc); add(writes, ra)
    elseif name == "CONCAT" then range(reads, rb, rc); add(writes, ra)
    elseif name == "NOT" or name == "MINUS" or name == "LENGTH" then add(reads, rb); add(writes, ra)
    elseif name == "SETLIST" then
        add(reads, ra)
        if rc == 0 then add(reads, rb); pack.openReadFrom = rb; pack.consumesTop = true
        elseif rc > 1 then range(reads, rb, rb + rc - 2) end
    elseif name == "FORNPREP" then
        range(reads, ra, ra + 2)


        range(writes, ra, ra + 2)
    elseif name == "FORNLOOP" then
        range(reads, ra, ra + 2); add(writes, ra + 2)
    elseif name == "FORGPREP" or name == "FORGPREP_INEXT" or name == "FORGPREP_NEXT" then
        range(reads, ra, ra + 2); range(writes, ra, ra + 2)
    elseif name == "FORGLOOP" then
        local count = bit32.band(aux, 0xff)
        range(reads, ra, ra + 2); add(writes, ra + 2)
        if count > 0 then range(writes, ra + 3, ra + 2 + count) end
    elseif name == "GETVARARGS" then
        if rb == 0 then add(writes, ra); pack.openWriteFrom = ra; pack.producesTop = true
        elseif rb > 1 then range(writes, ra, ra + rb - 2) end
    elseif name == "CAPTURE" then if ra == 0 or ra == 1 then add(reads, rb) end
    elseif name == "JUMPIF" or name == "JUMPIFNOT" or name == "JUMPXEQKNIL" or name == "JUMPXEQKB" or name == "JUMPXEQKN" or name == "JUMPXEQKS" or name == "CMPPROTO" then
        add(reads, ra)
    elseif name == "JUMPIFEQ" or name == "JUMPIFNOTEQ" or name == "JUMPIFLT" or name == "JUMPIFLE" or name == "JUMPIFNOTLT" or name == "JUMPIFNOTLE" then
        add(reads, ra); add(reads, bit32.band(aux, 0xff))
    elseif name == "NEWCLASSMEMBER" then add(reads, ra); add(reads, rc)
    elseif name == "NEWCLASS" then if rb ~= 0xff then add(reads, rb) end; add(writes, ra)
    end

    return reads, writes, pack
end

function regs.stats(proto, aux)
    local stats = {}
    aux = aux or ins.auxSlots(proto)
    local function get(reg)
        local entry = stats[reg]
        if not entry then
            entry = { reads = 0, writes = 0, firstWrite = nil, lastWrite = nil, firstRead = nil, lastRead = nil, firstAccess = nil, lastAccess = nil }
            stats[reg] = entry
        end
        return entry
    end
    for pc = 1, #proto.Instructions do
        if not aux[pc] then
            local reads, writes = regs.readWrite(proto.Instructions[pc])
            for reg in pairs(reads) do
                local e = get(reg); e.reads += 1; e.firstRead = e.firstRead or pc; e.lastRead = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
            end
            local name = ins.name(proto.Instructions[pc])
            for reg in pairs(writes) do
                if name ~= "NAMECALL" and name ~= "NAMECALLUDATA" then
                    local e = get(reg); e.writes += 1; e.firstWrite = e.firstWrite or pc; e.lastWrite = pc; e.firstAccess = e.firstAccess or pc; e.lastAccess = pc
                end
            end
        end
    end
    return stats
end

return regs
