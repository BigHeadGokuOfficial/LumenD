local util = {}

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
    local eq = s:sub(at):match("^%[(=*)%[")
    if eq == nil then return nil end
    local close = "]" .. eq .. "]"
    local _, b = s:find(close, at + #eq + 2, true)
    return b
end

function util.singlevalue(text)
    text = tostring(text or "")
    local round, square, brace = 0, 0, 0
    local quote
    local i = 1

    while i <= #text do
        local ch = text:sub(i, i)
        if quote then
            if ch == quote and not escaped(text, i) then quote = nil end
            i += 1
        else
            local lb = ch == "[" and longbracket(text, i) or nil
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
            elseif ch == "," and round == 0 and square == 0 and brace == 0 then
                return false
            else
                i += 1
            end
        end
    end

    return quote == nil and round == 0 and square == 0 and brace == 0
end

return util
