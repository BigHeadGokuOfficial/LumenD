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

local function render(v)
    if type(v) ~= "table" then return tostring(v) end
    local kind = v.kind
    if kind == "atom" or kind == "raw" or kind == "literal" or kind == "local" or kind == "global" then
        return tostring(v.value or "")
    elseif kind == "bin" then
        local p = v.p
        local function wrap(x, right)
            if type(x) ~= "table" then return tostring(x) end
            local text = render(x)
            if x.p < p then return "(" .. text .. ")" end
            if x.p == p then
                if p == 3 then return "(" .. text .. ")" end
                if v.op == "^" and not right then return "(" .. text .. ")" end
                if v.op == ".." and not right then return "(" .. text .. ")" end
                if right and v.op ~= "^" and v.op ~= ".." then return "(" .. text .. ")" end
            end
            return text
        end
        return wrap(v.a, false) .. " " .. v.op .. " " .. wrap(v.b, true)
    elseif kind == "un" then
        local a = render(v.a)
        if type(v.a) == "table" and v.a.p < v.p then a = "(" .. a .. ")" end
        return v.op == "not" and ("not " .. a) or (v.op .. a)
    elseif kind == "prop" then
        local a = render(v.a)
        if type(v.a) == "table" and v.a.p < 9 then a = "(" .. a .. ")" end
        return a .. tostring(v.field or "")
    elseif kind == "call" then
        local fn = render(v.fn)
        if type(v.fn) == "table" and v.fn.p < 9 then fn = "(" .. fn .. ")" end
        if v.method then fn = fn .. ":" .. tostring(v.method) end
        local args = {}
        for i, arg in ipairs(v.args or {}) do args[i] = render(arg) end
        return fn .. "(" .. table.concat(args, ", ") .. ")"
    elseif kind == "table" then
        local out = {}
        for _, field in ipairs(v.fields or {}) do
            if field.kind == "list" then
                out[#out + 1] = render(field.value)
            elseif field.kind == "field" then
                out[#out + 1] = tostring(field.key) .. " = " .. render(field.value)
            else
                out[#out + 1] = "[" .. tostring(field.key) .. "] = " .. render(field.value)
            end
        end
        return #out == 0 and "{}" or ("{ " .. table.concat(out, ", ") .. " }")
    end
    error("LumenV4: EXPR_VERIFY unknown semantic expression kind " .. tostring(kind), 2)
end

local function node(kind, p, stable, data)
    local out = { kind = kind, p = p or 99, stable = stable == true }
    for k, v in pairs(data or {}) do out[k] = v end
    out.s = render(out)
    return out
end

function expr.atom(s, stable)
    return node("atom", 99, stable, { value = s })
end

function expr.raw(s, stable)
    return node("raw", 99, stable, { value = s })
end

function expr.literal(s)
    return node("literal", 99, true, { value = s })
end

function expr.localref(symbol, name)
    return node("local", 99, false, { symbol = symbol, value = name })
end

function expr.global(name)
    return node("global", 99, false, { value = name })
end

function expr.bin(a, op, b)
    local p = prec[op] or 5
    return node("bin", p, type(a) == "table" and a.stable and type(b) == "table" and b.stable, { a = a, b = b, op = op })
end

function expr.un(op, a)
    return node("un", 7, type(a) == "table" and a.stable, { a = a, op = op })
end

function expr.prop(a, field)
    return node("prop", 10, false, { a = a, field = field })
end

function expr.call(fn, args, method)
    return node("call", 10, false, { fn = fn, args = args or {}, method = method })
end

function expr.table(fields)
    return node("table", 99, false, { fields = fields or {} })
end

function expr.join(list, op)
    local out = list[1]
    for i = 2, #list do out = expr.bin(out, op, list[i]) end
    return out
end

function expr.str(v)
    return render(v)
end

local function fmtcfg(opt)
    local f = opt and opt.formatter or {}
    local width = math.max(0, math.min(16, math.floor(tonumber(f.IndentWidth) or 4)))
    local maxline = math.max(40, math.floor(tonumber(f.MaxLineLength) or 110))
    local inline = math.max(1, math.floor(tonumber(f.TableInlineLimit) or 4))
    return width, maxline, inline
end

local function pretty(v, opt, depth)
    if type(v) ~= "table" or v.kind ~= "table" then return render(v) end

    local fields = v.fields or {}
    if #fields == 0 then return "{}" end

    local width, maxline, inline = fmtcfg(opt)
    local plain = render(v)
    local nested = false
    for _, field in ipairs(fields) do
        if type(field.value) == "table" and field.value.kind == "table" then
            nested = true
            break
        end
    end

    if not nested and #fields <= inline and (#plain + width * (depth or 0)) <= maxline then
        return plain
    end

    depth = depth or 0
    local innerindent = string.rep(" ", width * (depth + 1))
    local closeindent = string.rep(" ", width * depth)
    local out = { "{" }

    for _, field in ipairs(fields) do
        local prefix
        if field.kind == "list" then
            prefix = ""
        elseif field.kind == "field" then
            prefix = tostring(field.key) .. " = "
        else
            prefix = "[" .. tostring(field.key) .. "] = "
        end
        out[#out + 1] = innerindent .. prefix .. pretty(field.value, opt, depth + 1) .. ","
    end

    out[#out + 1] = closeindent .. "}"
    return table.concat(out, "\n")
end

function expr.format(v, opt, depth)
    return pretty(v, opt, depth or 0)
end

local function verify(v, seen)
    if type(v) ~= "table" then return true end
    seen = seen or {}
    if seen[v] then return true end
    seen[v] = true
    local kind = v.kind
    if kind == "local" then
        assert(v.symbol ~= nil, "LumenV4: EXPR_VERIFY local expression has no SymbolId")
        assert(type(v.value) == "string" and v.value ~= "", "LumenV4: EXPR_VERIFY local expression has no display name")
    elseif kind == "global" or kind == "literal" or kind == "atom" or kind == "raw" then
        assert(v.value ~= nil, "LumenV4: EXPR_VERIFY atom has no value")
    elseif kind == "bin" then
        assert(v.op and v.a ~= nil and v.b ~= nil, "LumenV4: EXPR_VERIFY malformed binary expression")
        verify(v.a, seen); verify(v.b, seen)
    elseif kind == "un" then
        assert(v.op and v.a ~= nil, "LumenV4: EXPR_VERIFY malformed unary expression")
        verify(v.a, seen)
    elseif kind == "prop" then
        assert(v.a ~= nil and v.field ~= nil, "LumenV4: EXPR_VERIFY malformed property expression")
        verify(v.a, seen)
    elseif kind == "call" then
        assert(v.fn ~= nil and type(v.args) == "table", "LumenV4: EXPR_VERIFY malformed call expression")
        verify(v.fn, seen); for _, a in ipairs(v.args) do verify(a, seen) end
    elseif kind == "table" then
        for _, field in ipairs(v.fields or {}) do
            assert(field.value ~= nil, "LumenV4: EXPR_VERIFY table field has no value")
            verify(field.value, seen)
        end
    else
        error("LumenV4: EXPR_VERIFY unknown expression kind " .. tostring(kind), 2)
    end
    assert(render(v) == v.s, "LumenV4: EXPR_VERIFY cached rendering diverged from semantic tree")
    return true
end

expr.verify = verify
return expr
