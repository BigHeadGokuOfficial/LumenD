local util = {}

local inverse = {
    ["=="] = "~=",
    ["~="] = "==",
    ["<"] = ">=",
    ["<="] = ">",
    [">"] = "<=",
    [">="] = "<",
}

local function trim(s)
    return (tostring(s or ""):gsub("^%s+", ""):gsub("%s+$", ""))
end

local function escaped(s, at)
    local n = 0
    at -= 1
    while at >= 1 and s:sub(at, at) == "\\" do
        n += 1
        at -= 1
    end
    return n % 2 == 1
end

local function longbracket(s, at)
    if s:sub(at, at) ~= "[" then return nil end
    local rest = s:sub(at)
    local eq = rest:match("^%[(=*)%[")
    if eq == nil then return nil end
    local close = "]" .. eq .. "]"
    local first = at + #eq + 2
    local _, b = s:find(close, first, true)
    return b
end

local function wordat(s, at, word)
    if s:sub(at, at + #word - 1) ~= word then return false end
    local before = at > 1 and s:sub(at - 1, at - 1) or ""
    local after = s:sub(at + #word, at + #word)
    if before:match("[%w_]") or after:match("[%w_]") then return false end
    return true
end

local function topcmp(s)
    local round, square, brace = 0, 0, 0
    local quote
    local candidateAt, candidateOp
    local i = 1
    while i <= #s do
        local ch = s:sub(i, i)
        if quote then
            if ch == quote and not escaped(s, i) then quote = nil end
            i += 1
        else
            local lb = ch == "[" and longbracket(s, i) or nil
            if lb then
                i = lb + 1
            elseif ch == "'" or ch == '"' or ch == "`" then
                quote = ch
                i += 1
            elseif ch == "(" then
                round += 1
                i += 1
            elseif ch == ")" then
                round = math.max(0, round - 1)
                i += 1
            elseif ch == "[" then
                square += 1
                i += 1
            elseif ch == "]" then
                square = math.max(0, square - 1)
                i += 1
            elseif ch == "{" then
                brace += 1
                i += 1
            elseif ch == "}" then
                brace = math.max(0, brace - 1)
                i += 1
            elseif round == 0 and square == 0 and brace == 0 then
                if wordat(s, i, "and") or wordat(s, i, "or") then return nil end
                local two = s:sub(i, i + 1)
                local op
                if inverse[two] then
                    op = two
                elseif inverse[ch] then
                    op = ch
                end
                if op and not candidateAt then candidateAt, candidateOp = i, op end
                i += 1
            else
                i += 1
            end
        end
    end
    return candidateAt, candidateOp
end

local function outerparen(s)
    if s:sub(1, 1) ~= "(" or s:sub(-1) ~= ")" then return false end
    local depth = 0
    local quote
    local i = 1
    while i <= #s do
        local ch = s:sub(i, i)
        if quote then
            if ch == quote and not escaped(s, i) then quote = nil end
            i += 1
        else
            local lb = ch == "[" and longbracket(s, i) or nil
            if lb then
                i = lb + 1
            elseif ch == "'" or ch == '"' or ch == "`" then
                quote = ch
                i += 1
            elseif ch == "(" then
                depth += 1
                i += 1
            elseif ch == ")" then
                depth -= 1
                if depth == 0 and i ~= #s then return false end
                if depth < 0 then return false end
                i += 1
            else
                i += 1
            end
        end
    end
    return depth == 0
end

function util.strip(s)
    s = trim(s)
    while outerparen(s) do
        s = trim(s:sub(2, -2))
    end
    return s
end

function util.negate(s)
    s = util.strip(s)
    if s == "true" then return "false" end
    if s == "false" then return "true" end

    local at, op = topcmp(s)
    if at and op then
        local a = trim(s:sub(1, at - 1))
        local b = trim(s:sub(at + #op))
        if a ~= "" and b ~= "" then
            return a .. " " .. inverse[op] .. " " .. b
        end
    end

    if s:sub(1, 4) == "not " then
        local rest = trim(s:sub(5))
        if outerparen(rest) then return util.strip(rest) end
        if rest:match("^[%a_][%w_%.]*$") then return rest end
    end

    return "not (" .. s .. ")"
end

function util.simplify(s)
    s = trim(s)
    if s:sub(1, 4) ~= "not " then return s end
    local rest = trim(s:sub(5))
    if not outerparen(rest) then return s end
    return util.negate(util.strip(rest))
end

return util
