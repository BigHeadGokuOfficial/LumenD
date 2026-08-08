local fx = {}

local pure = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, GETIMPORT = true, GETGLOBAL = true,
    GETTABLE = true, GETTABLEKS = true, GETTABLEN = true, GETUDATAKS = true,
    ADD = true, SUB = true, MUL = true, DIV = true, MOD = true, POW = true,
    IDIV = true, ADDK = true, SUBK = true, MULK = true, DIVK = true,
    MODK = true, POWK = true, IDIVK = true, SUBRK = true, DIVRK = true,
    AND = true, OR = true, ANDK = true, ORK = true, CONCAT = true,
    NOT = true, MINUS = true, LENGTH = true, NEWTABLE = true, DUPTABLE = true,
    GETVARARGS = true,
}

local drop = {
    LOADNIL = true, LOADB = true, LOADN = true, LOADK = true, LOADKX = true,
    MOVE = true, GETUPVAL = true, AND = true, OR = true, ANDK = true, ORK = true,
    NOT = true, NEWTABLE = true, DUPTABLE = true, GETVARARGS = true,
}

local quiet = {
    NOP = true, LOADNIL = true, LOADB = true, LOADN = true, LOADK = true,
    LOADKX = true, MOVE = true, GETUPVAL = true, PREPVARARGS = true,
    COVERAGE = true,
}

local term = {
    RETURN = true, JUMP = true, JUMPBACK = true, JUMPX = true,
    JUMPIF = true, JUMPIFNOT = true, JUMPIFEQ = true, JUMPIFNOTEQ = true,
    JUMPIFLT = true, JUMPIFLE = true, JUMPIFNOTLT = true, JUMPIFNOTLE = true,
    JUMPXEQKNIL = true, JUMPXEQKB = true, JUMPXEQKN = true, JUMPXEQKS = true,
    FORNPREP = true, FORNLOOP = true, FORGPREP = true, FORGPREP_INEXT = true,
    FORGPREP_NEXT = true, FORGLOOP = true, CMPPROTO = true,
}

function fx.pure(name)
    return pure[name] == true
end

function fx.drop(name)
    return drop[name] == true
end

function fx.quiet(name)
    return quiet[name] == true
end

function fx.term(name)
    return term[name] == true
end

function fx.effect(name)
    if drop[name] or quiet[name] or term[name] then return false end
    if name == "NOP" or name == "BREAK" or name == "CLOSEUPVALS" or name == "PREPVARARGS" or name == "COVERAGE" or name == "NATIVECALL" or name == "CAPTURE" then return false end
    return true
end

return fx