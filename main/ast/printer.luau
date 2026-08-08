
local printast = {}

local function esc(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function hasname(node, name)
    if not node or node.dead then return false end
    local pat = "%f[%w_]" .. esc(name) .. "%f[^%w_]"
    local function hit(s) return type(s) == "string" and s:find(pat) ~= nil end
    if hit(node.text) or hit(node.cond) or hit(node.head) or hit(node.args) then return true end
    if node.kind == "if" then
        for _, b in ipairs(node.branches or {}) do
            if hit(b.cond) then return true end
            for _, x in ipairs(b.body.body or {}) do if hasname(x, name) then return true end end
        end
        if node.elsebody then for _, x in ipairs(node.elsebody.body or {}) do if hasname(x, name) then return true end end end
    elseif node.body then
        for _, x in ipairs(node.body.body or {}) do if hasname(x, name) then return true end end
    end
    return false
end

local function recursive(node)
    for _, x in ipairs(node.body.body or {}) do if hasname(x, node.name) then return true end end
    return false
end

local function indent(opt, depth)
    local n = tonumber(opt.formatter and opt.formatter.IndentWidth) or 4
    n = math.max(0, math.min(16, math.floor(n)))
    return string.rep(" ", n * depth)
end

local function line(out, opt, depth, s, stmt)
    if stmt and opt.formatter and opt.formatter.AppendSemicolons then
        local last = s:sub(-1)
        if last ~= ";" and last ~= ":" then s = s .. ";" end
    end
    out[#out + 1] = indent(opt, depth) .. s
end

local function cond(opt, s)
    if opt.formatter and opt.formatter.ParenthesizeConditions then return "(" .. s .. ")" end
    return s
end

local function fnhead(node, opt)
    local args = node.args or ""
    if opt.functions == false then
        if node.localfn then return "local " .. node.name .. " = function(" .. args .. ")" end
        if node.assign then return node.name .. " = function(" .. args .. ")" end
        local base, field = node.name:match("^(.*):([%a_][%w_]*)$")
        if base and field then
            local a = args ~= "" and ("self, " .. args) or "self"
            return base .. "." .. field .. " = function(" .. a .. ")"
        end
        return node.name .. " = function(" .. args .. ")"
    end
    if node.localfn then return "local function " .. node.name .. "(" .. args .. ")" end
    if node.assign then return node.name .. " = function(" .. args .. ")" end
    return "function " .. node.name .. "(" .. args .. ")"
end

local function block(out, b, depth, opt)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, opt, depth, node.text, true)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, opt, depth, (i == 1 and "if " or "elseif ") .. cond(opt, branch.cond) .. " then")
                    block(out, branch.body, depth + 1, opt)
                end
                if node.elsebody then
                    line(out, opt, depth, "else")
                    block(out, node.elsebody, depth + 1, opt)
                end
                line(out, opt, depth, "end")
            elseif k == "while" then
                line(out, opt, depth, "while " .. cond(opt, node.cond) .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "repeat" then
                line(out, opt, depth, "repeat")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "until " .. cond(opt, node.cond))
            elseif k == "for" then
                line(out, opt, depth, node.head .. " do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "do" then
                line(out, opt, depth, "do")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end")
            elseif k == "callback" then
                line(out, opt, depth, node.pre .. "function(" .. node.args .. ")")
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end" .. node.post, true)
            elseif k == "function" then
                if opt.functions == false and node.localfn and recursive(node) then
                    line(out, opt, depth, "local " .. node.name, true)
                    line(out, opt, depth, node.name .. " = function(" .. (node.args or "") .. ")")
                else
                    line(out, opt, depth, fnhead(node, opt))
                end
                block(out, node.body, depth + 1, opt)
                line(out, opt, depth, "end", opt.functions == false or node.assign)
            end
        end
    end
end

function printast.run(root, opt)
    opt = opt or {}
    local out = {}
    block(out, root, 0, opt)
    return table.concat(out, "\n")
end

return printast
