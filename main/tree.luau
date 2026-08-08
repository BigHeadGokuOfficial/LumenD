local tree = {}

local win = {
    CON = true, PRN = true, AUX = true, NUL = true,
    COM1 = true, COM2 = true, COM3 = true, COM4 = true, COM5 = true,
    COM6 = true, COM7 = true, COM8 = true, COM9 = true,
    LPT1 = true, LPT2 = true, LPT3 = true, LPT4 = true, LPT5 = true,
    LPT6 = true, LPT7 = true, LPT8 = true, LPT9 = true,
}

local cls = { LocalScript = true, ModuleScript = true, Script = true }

local function hash(s)
    local h = 7
    for i = 1, #s do
        h = (h * 131 + s:byte(i)) % 2147483647
    end
    return string.format("%08x", h)
end

local function clean(s)
    s = tostring(s or "")
    s = s:gsub("[%z\1-\31]", "_")
    s = s:gsub('[<>:"/\\|%?%*]', "_")
    s = s:gsub("[%.%s]+$", "")
    if s == "" then s = "_unnamed" end
    local b = s:match("^([^%.]+)") or s
    if win[b:upper()] then s = "_" .. s end
    if #s > 80 then s = s:sub(1, 71) .. "_" .. hash(s) end
    return s
end

local function kids(obj)
    local ok, out = pcall(obj.GetChildren, obj)
    if not ok or type(out) ~= "table" then return nil, out end
    return out
end

local function iscript(obj)
    local ok, c = pcall(function() return obj.ClassName end)
    return ok and cls[c] == true
end

local function mk(path, made)
    if made[path] then return true end
    if type(isfolder) == "function" then
        local ok, yes = pcall(isfolder, path)
        if ok and yes then
            made[path] = true
            return true
        end
    end
    if type(makefolder) ~= "function" then return false end
    local ok = pcall(makefolder, path)
    if ok then made[path] = true end
    return ok
end

local function mkall(path, made)
    local cur = ""
    for p in tostring(path):gmatch("[^/]+") do
        cur = cur == "" and p or cur .. "/" .. p
        if not mk(cur, made) then return false end
    end
    return true
end

local function extname(s)
    local low = s:lower()
    if low:sub(-5) == ".luau" or low:sub(-4) == ".lua" then return s end
    return s .. ".luau"
end

local function numbered(s, n)
    local stem, ext = s:match("^(.*)(%.luau)$")
    if not stem then stem, ext = s:match("^(.*)(%.lua)$") end
    if not stem then return s .. "__" .. tostring(n) end
    return stem .. "__" .. tostring(n) .. ext
end

local function build(parent, ctx)
    local hit = ctx.idx[parent]
    if hit then return hit end
    local list, err = kids(parent)
    local out = { seg = {}, file = {}, err = err }
    ctx.idx[parent] = out
    if not list then return out end

    local seen = {}
    for _, obj in ipairs(list) do
        if ctx.dirinst[obj] then
            local base = clean(obj.Name)
            local key = base:lower()
            local n = (seen[key] or 0) + 1
            seen[key] = n
            out.seg[obj] = n == 1 and base or base .. "__" .. tostring(n)
        end
    end

    local used = {}
    for _, name in pairs(out.seg) do used[name:lower()] = true end
    for _, obj in ipairs(list) do
        if ctx.scriptset[obj] then
            local base = extname(clean(obj.Name))
            local name = base
            local n = 2
            while used[name:lower()] do
                name = numbered(base, n)
                n = n + 1
            end
            used[name:lower()] = true
            out.file[obj] = name
        end
    end
    return out
end

local function seg(obj, ctx)
    local p = obj and obj.Parent
    if not p then return clean(obj and obj.Name) end
    local x = build(p, ctx)
    return x.seg[obj] or clean(obj.Name)
end

local function file(obj, ctx)
    local p = obj.Parent
    if p then
        local x = build(p, ctx)
        if x.file[obj] then return x.file[obj] end
    end
    return extname(clean(obj.Name))
end

local function rel(obj, ctx)
    local rev = {}
    local cur = obj.Parent
    while cur and cur ~= game do
        rev[#rev + 1] = seg(cur, ctx)
        cur = cur.Parent
    end
    local out = {}
    for i = #rev, 1, -1 do out[#out + 1] = rev[i] end
    return out
end

local function flat(obj, ctx)
    local p = rel(obj, ctx)
    p[#p + 1] = file(obj, ctx)
    return table.concat(p, "__")
end

local function short(ctx, path, name)
    if #path <= ctx.max then return path end
    local dir = ctx.root .. "/_LongPaths"
    mkall(dir, ctx.made)
    local stem, ext = name:match("^(.*)(%.luau)$")
    if not stem then stem, ext = name:match("^(.*)(%.lua)$") end
    stem = stem or name
    ext = ext or ".luau"
    local n = stem:sub(1, 50) .. "_" .. hash(path) .. ext
    return dir .. "/" .. n
end

local function full(obj)
    local ok, s = pcall(obj.GetFullName, obj)
    if ok and type(s) == "string" then return s end
    return tostring(obj.Name)
end

local function one(s)
    return tostring(s or ""):gsub("[\r\n\t]", " ")
end

function tree.new(root, made, max, list)
    local ctx = {
        root = root,
        made = made or {},
        max = tonumber(max) or 240,
        idx = {},
        map = {},
        dirinst = {},
        scriptset = {},
    }
    for _, obj in ipairs(list or {}) do
        ctx.scriptset[obj] = true
        local cur = obj.Parent
        while cur and cur ~= game do
            ctx.dirinst[cur] = true
            cur = cur.Parent
        end
    end
    return ctx
end

function tree.path(ctx, obj, treeon)
    local dir = ctx.root
    local name
    if treeon then
        local p = rel(obj, ctx)
        if #p > 0 then dir = dir .. "/" .. table.concat(p, "/") end
        name = file(obj, ctx)
    else
        dir = ctx.root .. "/Scripts"
        name = flat(obj, ctx)
    end
    mkall(dir, ctx.made)
    return short(ctx, dir .. "/" .. name, name)
end

function tree.record(ctx, obj, path, state)
    ctx.map[#ctx.map + 1] = table.concat({
        one(state), one(obj.ClassName), one(full(obj)), one(path)
    }, "\t")
end

function tree.map(ctx)
    local out = { "status\tclass\troblox_path\tfile" }
    for _, line in ipairs(ctx.map) do out[#out + 1] = line end
    return table.concat(out, "\n")
end

function tree.placeholder(obj, v)
    local state = v and v.unavailable and "source unavailable" or "decompile failed"
    local reason = one(v and v.error or "unknown error")
    return "-- LumenDecomp: " .. state .. "\n-- Path: " .. one(full(obj)) .. "\n-- Class: " .. one(obj.ClassName) .. "\n-- Reason: " .. reason .. "\n"
end

function tree.scan(ignore, core)
    local out = {}
    local errors = {}
    local roots, err = kids(game)
    if not roots then return out, { "game :: " .. tostring(err) } end
    local stack = {}
    for i = #roots, 1, -1 do stack[#stack + 1] = roots[i] end

    while #stack > 0 do
        local obj = stack[#stack]
        stack[#stack] = nil
        local skip = false
        if ignore and core then
            local ok, yes = pcall(core.is, obj)
            skip = ok and yes == true
        end
        if not skip then
            if iscript(obj) then out[#out + 1] = obj end
            local list, e = kids(obj)
            if list then
                for i = #list, 1, -1 do stack[#stack + 1] = list[i] end
            else
                errors[#errors + 1] = full(obj) .. " :: " .. tostring(e)
            end
        end
    end
    return out, errors
end

function tree.mkall(path, made)
    return mkall(path, made)
end

function tree.clean(s)
    return clean(s)
end

function tree.script(obj)
    return iscript(obj)
end

return tree
