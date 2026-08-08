
local ins = {}

local conditional = {
    JUMPIF = true,
    JUMPIFNOT = true,
    JUMPIFEQ = true,
    JUMPIFNOTEQ = true,
    JUMPIFLT = true,
    JUMPIFLE = true,
    JUMPIFNOTLT = true,
    JUMPIFNOTLE = true,
    JUMPXEQKNIL = true,
    JUMPXEQKB = true,
    JUMPXEQKN = true,
    JUMPXEQKS = true,
    CMPPROTO = true,
    FORNLOOP = true,
    FORGLOOP = true,
}

local jumps = {
    JUMP = true,
    JUMPBACK = true,
    JUMPX = true,
    FORGPREP = true,
    FORGPREP_INEXT = true,
    FORGPREP_NEXT = true,
}

function ins.name(op)
    return op and op.OpCodeInfo and op.OpCodeInfo.Name or "?"
end

function ins.auxSlots(proto)
    local slots = {}

    for pc = 1, #proto.Instructions do
        if not slots[pc] then
            local op = proto.Instructions[pc]
            if op and op.OpCodeInfo and op.OpCodeInfo.HasAux then
                slots[pc + 1] = true
            end
        end
    end

    return slots
end

function ins.next(proto, pc, auxSlots)
    auxSlots = auxSlots or ins.auxSlots(proto)
    local op = proto.Instructions[pc]

    if not op then
        return pc + 1
    end

    return pc + ((op.OpCodeInfo and op.OpCodeInfo.HasAux) and 2 or 1)
end

function ins.jumpTarget(pc, op)
    if ins.name(op) == "JUMPX" then
        return pc + (op.E or 0) + 1
    end

    return pc + (op.D or 0) + 1
end

function ins.isConditional(op)
    return conditional[ins.name(op)] == true
end

function ins.isUnconditional(op)
    return jumps[ins.name(op)] == true
end

function ins.previousRealPC(auxSlots, pc)
    pc = pc - 1
    while pc >= 1 do
        if not auxSlots[pc] then
            return pc
        end
        pc = pc - 1
    end
end

return ins
