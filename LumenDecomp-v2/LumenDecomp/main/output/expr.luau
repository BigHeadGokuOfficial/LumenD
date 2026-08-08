local expr = {}

local prec = {
    ["or"] = 1,
    ["and"] = 2,
    ["=="] = 3,
    ["~="] = 3,
    ["<"] = 3,
    ["<="] = 3,
    [">"] = 3,
    [">="] = 3,
    [".."] = 4,
    ["+"] = 5,
    ["-"] = 5,
    ["*"] = 6,
    ["/"] = 6,
    ["//"] = 6,
    ["%"] = 6,
    ["^"] = 8,
}

local function node(s, p, stable, kind, a, b, op)
    return { s = s, p = p or 99, stable = stable == true, kind = kind, a = a, b = b, op = op }
end

local function text(v)
    return type(v) == "table" and v.s or tostring(v)
end

local function wrap(v, p, right, op)
    if type(v) ~= "table" then return tostring(v) end
    if v.p < p then return "(" .. v.s .. ")" end
    if v.p == p then
        if p == 3 then return "(" .. v.s .. ")" end
        if op == "^" and not right then return "(" .. v.s .. ")" end
        if op == ".." and not right then return "(" .. v.s .. ")" end
        if right and op ~= "^" and op ~= ".." then return "(" .. v.s .. ")" end
    end
    return v.s
end

function expr.atom(s, stable)
    return node(s, 99, stable, "atom")
end

function expr.bin(a, op, b)
    local p = prec[op] or 5
    return node(wrap(a, p, false, op) .. " " .. op .. " " .. wrap(b, p, true, op), p, a.stable and b.stable, "bin", a, b, op)
end

function expr.un(op, a)
    local p = 7
    local s = type(a) == "table" and (a.p < p and "(" .. a.s .. ")" or a.s) or tostring(a)
    if op == "not" then
        return node("not " .. s, p, a.stable, "un", a, nil, op)
    end
    return node(op .. s, p, a.stable, "un", a, nil, op)
end

function expr.prop(a, field)
    local base = type(a) == "table" and (a.p < 9 and "(" .. a.s .. ")" or a.s) or tostring(a)
    return node(base .. field, 10, false, "prop", a, field)
end

function expr.call(fn, args, method)
    local base = type(fn) == "table" and (fn.p < 9 and "(" .. fn.s .. ")" or fn.s) or tostring(fn)
    if method then base = base .. ":" .. method end
    return node(base .. "(" .. table.concat(args, ", ") .. ")", 10, false, "call", fn, args, method)
end

function expr.join(list, op)
    local out = list[1]
    for i = 2, #list do out = expr.bin(out, op, list[i]) end
    return out
end

function expr.str(v)
    return text(v)
end

return expr
