local env = require("main.runtime.environment")
local st = require("main.runtime.status")

local dump = {}

local function clean(s)
    s = tostring(s or "unnamed")
    s = s:gsub("[%c<>:\"/\\|%?%*]", "_")
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    if s == "" or s == "." or s == ".." then s = "unnamed" end
    return s
end

local function mkdir(path, made)
    if made[path] then return true end
    if type(makefolder) ~= "function" then return false end
    if type(isfolder) == "function" then
        local ok, yes = pcall(isfolder, path)
        if ok and yes then
            made[path] = true
            return true
        end
    end
    local ok = pcall(makefolder, path)
    if ok then made[path] = true end
    return ok
end

local function mkall(path, made)
    local cur = ""
    for part in tostring(path):gmatch("[^/]+") do
        cur = cur == "" and part or cur .. "/" .. part
        mkdir(cur, made)
    end
end

local function rootdir()
    return "LumenDecomp/" .. tostring(game.PlaceId or 0) .. "/dump_" .. tostring(os.time())
end

local function scriptobj(obj)
    local c = obj.ClassName
    return c == "LocalScript" or c == "ModuleScript" or c == "Script"
end

local function parts(obj)
    local rev = {}
    local cur = obj.Parent
    while cur and cur ~= game do
        rev[#rev + 1] = clean(cur.Name)
        cur = cur.Parent
    end
    local out = {}
    for i = #rev, 1, -1 do out[#out + 1] = rev[i] end
    return out
end

local function outpath(root, obj, flat, used, made)
    local seg = parts(obj)
    local dir = root .. "/Scripts"

    if not flat then
        for _, name in ipairs(seg) do dir = dir .. "/" .. name end
    end

    mkall(dir, made)

    local base = clean(obj.Name) .. "." .. clean(obj.ClassName)
    if flat then
        local full = st.path(obj):gsub("%.", "_")
        base = clean(full) .. "." .. clean(obj.ClassName)
    end

    local path = dir .. "/" .. base .. ".luau"
    local n = 2
    while used[path] do
        path = dir .. "/" .. base .. "_" .. tostring(n) .. ".luau"
        n += 1
    end
    used[path] = true
    return path
end

local core = {
    CoreGui = true,
    CorePackages = true,
    RobloxReplicatedStorage = true,
    CoreScriptSyncService = true,
}

local function scripts(ignorecore)
    local out = {}
    for _, root in ipairs(game:GetChildren()) do
        if not (ignorecore and core[root.Name]) then
            if scriptobj(root) then out[#out + 1] = root end
            for _, obj in ipairs(root:GetDescendants()) do
                if scriptobj(obj) then out[#out + 1] = obj end
            end
        end
    end
    return out
end

local function write(path, data)
    if type(writefile) ~= "function" then
        return false, "executor does not expose writefile()"
    end
    local ok, err = pcall(writefile, path, data)
    return ok, err
end

local function decompileall(lumen, list, opt, stat)
    local cache = {}
    local started = os.clock()
    local total = #list

    stat.found = total

    local decopt = { metadata = false }
    if type(opt.Options) == "table" then
        for k, v in pairs(opt.Options) do decopt[k] = v end
        decopt.metadata = false
    end

    for i, obj in ipairs(list) do
        local res = lumen:tryDecompile(obj, decopt)

        if res.success and type(res.source) == "string" and res.source ~= "" then
            cache[obj] = res.source
            stat.good += 1
        else
            local err = tostring(res.error)
            cache[obj] = { success = false, error = err }
            stat.failed += 1
            stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. err
        end

        local elapsed = os.clock() - started
        local rate = elapsed > 0 and i / elapsed or nil
        st.progress("Decompiling", obj, i, total, rate)
    end

    stat.decompileTime = os.clock() - started
    stat.rate = stat.decompileTime > 0 and total / stat.decompileTime or 0
    return cache
end

local function writetree(root, list, cache, treeon, stat, made)
    local used = {}
    local total = #list
    local started = os.clock()

    for i, obj in ipairs(list) do
        local src = cache[obj]
        if type(src) == "string" then
            local path = outpath(root, obj, not treeon, used, made)
            local ok, err = write(path, src)
            if not ok then
                stat.writeFailed += 1
                stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. tostring(err)
            end
        end

        local elapsed = os.clock() - started
        local rate = elapsed > 0 and i / elapsed or nil
        st.progress("Writing source tree", obj, i, total, rate)
    end

    stat.writeTime = os.clock() - started
end

local function summary(root, stat)
    local lines = {
        "LumenDecomp dump",
        "PlaceId: " .. tostring(game.PlaceId),
        "Scripts found: " .. tostring(stat.found),
        "Decompiled: " .. tostring(stat.good),
        "Failed/skipped: " .. tostring(stat.failed),
        "Write failures: " .. tostring(stat.writeFailed),
        "Binary: " .. tostring(stat.binary),
        "Decompile seconds: " .. string.format("%.3f", stat.decompileTime or 0),
        "Decompile rate: " .. string.format("%.2f scripts/s", stat.rate or 0),
        "Write seconds: " .. string.format("%.3f", stat.writeTime or 0),
        "",
    }

    if #stat.errors > 0 then
        lines[#lines + 1] = "Errors:"
        for _, e in ipairs(stat.errors) do lines[#lines + 1] = e end
    end

    write(root .. "/summary.txt", table.concat(lines, "\n"))
end

function dump.run(lumen, opt)
    opt = opt or {}
    local root = opt.Root or rootdir()
    local stat = {
        found = 0,
        good = 0,
        failed = 0,
        writeFailed = 0,
        binary = false,
        errors = {},
        decompileTime = 0,
        writeTime = 0,
        rate = 0,
    }
    local made = {}

    mkall(root, made)
    st.set("Starting", tostring(game.Name) .. " | " .. root)

    local list
    local cache

    if opt.Decompile and (opt.Tree or not opt.Binary) then
        list = scripts(opt.IgnoreCoreScripts == true)
        cache = decompileall(lumen, list, opt, stat)
        writetree(root, list, cache, opt.Tree, stat, made)
    end

    if opt.Binary then
        st.set("Saving binary", cache and "reusing decompiled source cache" or tostring(game.Name))
        local file = root .. "/FullGame.rbxl"
        local ok, err = pcall(function()
            lumen:save(game, file, {
                Binary = true,
                Decompile = opt.Decompile == true,
                SourceCache = cache,
                NilInstances = opt.NilInstances == true,
                RemovePlayerCharacters = opt.RemovePlayerCharacters == true,
                SavePlayers = opt.SavePlayers == true,
                MaxThreads = opt.MaxThreads or 8,
                DecompileIgnore = opt.IgnoreCoreScripts and { "CoreGui", "CorePackages", "RobloxReplicatedStorage", "CoreScriptSyncService" } or opt.DecompileIgnore,
                ShowStatus = false,
            })
        end)
        stat.binary = ok
        if not ok then
            stat.errors[#stat.errors + 1] = "binary :: " .. tostring(err)
        end
    end

    summary(root, stat)
    st.done("Done — " .. tostring(stat.good) .. " decompiled, " .. tostring(stat.failed) .. " failed | " .. string.format("%.1f/s", stat.rate or 0))
    return root, stat
end

function dump.auto(lumen, boot)
    local e = env.get()

    local function flag(name)
        if type(boot) == "table" and boot[name] ~= nil then return boot[name] == true end

        local v = rawget(e, name)
        if v ~= nil then return v == true end

        if type(getfenv) == "function" then
            for level = 0, 8 do
                local ok, scope = pcall(getfenv, level)
                if ok and type(scope) == "table" then
                    v = rawget(scope, name)
                    if v ~= nil then return v == true end
                end
            end
        end

        v = rawget(_G, name)
        return v == true
    end

    local binary = flag("Binary")
    local decomp = flag("Decompile")
    local treeon = flag("Tree")
    local ignorecore = flag("IgnoreCoreScripts")
    local flags = "Binary=" .. tostring(binary) .. " | Decompile=" .. tostring(decomp) .. " | Tree=" .. tostring(treeon) .. " | IgnoreCoreScripts=" .. tostring(ignorecore)

    st.set("Loaded", "v" .. tostring(lumen.Version) .. " | " .. flags)
    print("[LumenDecomp] " .. flags)

    if not binary and not decomp and not treeon then
        task.delay(2, function() st.done("Loaded — idle | " .. flags) end)
        return false
    end

    if rawget(e, "__LumenDump") then
        st.set("Already running")
        return false
    end

    e.__LumenDump = true
    st.set("Starting dump", flags)
    task.spawn(function()
        local ok, err = pcall(function()
            dump.run(lumen, {
                Binary = binary,
                Decompile = decomp,
                Tree = treeon,
                IgnoreCoreScripts = ignorecore,
            })
        end)
        e.__LumenDump = nil
        if not ok then
            st.set("ERROR", tostring(err))
            warn("[LumenDecomp] " .. tostring(err))
        end
    end)
    return true
end

return dump
