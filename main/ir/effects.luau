
local fx = {}

local relocatable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,

    MOVE = true,
}

local discardable = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true, MOVE = true,
    NOT = true, AND = true, OR = true, ANDK = true, ORK = true,


}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, PREPVARARGS = true, COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

local effects = {
    GETGLOBAL = "ReadGlobal", SETGLOBAL = "WriteGlobal",
    GETUPVAL = "ReadCell", SETUPVAL = "WriteCell", CLOSEUPVALS = "CloseCells", CAPTURE = "CaptureCell",
    GETTABLE = "ReadTable", GETTABLEKS = "ReadTable", GETTABLEN = "ReadTable", GETUDATAKS = "ReadTable",
    SETTABLE = "WriteTable", SETTABLEKS = "WriteTable", SETTABLEN = "WriteTable", SETUDATAKS = "WriteTable",
    CALL = "CallUnknown", CALLFB = "CallUnknown", NAMECALL = "ReadTable", NAMECALLUDATA = "ReadTable",
    NEWCLOSURE = "AllocateClosure", DUPCLOSURE = "AllocateClosure",
    NEWTABLE = "AllocateObject", DUPTABLE = "AllocateObject", NEWCLASS = "AllocateObject", NEWCLASSMEMBER = "WriteTable",
    ADD = "MayMetamethod", SUB = "MayMetamethod", MUL = "MayMetamethod", DIV = "MayMetamethod", MOD = "MayMetamethod",
    POW = "MayMetamethod", IDIV = "MayMetamethod", ADDK = "MayMetamethod", SUBK = "MayMetamethod", MULK = "MayMetamethod",
    DIVK = "MayMetamethod", MODK = "MayMetamethod", POWK = "MayMetamethod", IDIVK = "MayMetamethod",
    SUBRK = "MayMetamethod", DIVRK = "MayMetamethod", CONCAT = "MayMetamethod", LENGTH = "MayMetamethod",
    GETIMPORT = "ReadImport", NATIVECALL = "CallUnknown",
}

function fx.pure(name) return relocatable[name] == true end
function fx.drop(name) return discardable[name] == true end
function fx.quiet(name) return quiet[name] == true end
function fx.term(name) return term[name] == true end
function fx.class(name)
    if term[name] then return "Control" end
    return effects[name] or (quiet[name] and "Pure" or "Unknown")
end
function fx.effect(name)
    local c = fx.class(name)
    return c ~= "Pure" and c ~= "Control"
end
function fx.canRelocate(name) return relocatable[name] == true end

return fx
