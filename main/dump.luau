local env = require("main.runtime.environment")
local st = require("main.runtime.status")
local coref = require("main.runtime.core")

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

local function scripts(ignorecore)
    local out = {}
    for _, root in ipairs(game:GetChildren()) do
        if not (ignorecore and coref.root(root)) then
            if scriptobj(root) and not (ignorecore and coref.is(root)) then out[#out + 1] = root end
            local ok, list = pcall(root.GetDescendants, root)
            if ok then
                for _, obj in ipairs(list) do
                    if scriptobj(obj) and not (ignorecore and coref.is(obj)) then out[#out + 1] = obj end
                end
            end
        end
    end
    return out
end

local function write(path, data)
    if type(writefile) ~= "function" then return false, "executor does not expose writefile()" end
    local ok, err = pcall(writefile, path, data)
    return ok, err
end

local function fail(stat, obj, err)
    err = tostring(err)
    stat.failed += 1
    local line = st.path(obj) .. " :: " .. err
    stat.errors[#stat.errors + 1] = line
    if stat.failed <= 5 then
        if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] FAIL " .. line .. "\n") end
        warn("[LumenDecomp] FAIL " .. line)
    end
end

local function serial(lumen, list, opt, stat)
    local cache = {}
    local started = os.clock()
    local total = #list
    local decopt = {}
    if type(opt.Options) == "table" then
        for k, v in pairs(opt.Options) do decopt[k] = v end
    end
    stat.found = total
    for i, obj in ipairs(list) do
        local res = lumen:tryDecompile(obj, decopt)
        if res.success and type(res.source) == "string" and res.source ~= "" then
            cache[obj] = res.source
            stat.good += 1
        else
            fail(stat, obj, res.error)
        end
        local elapsed = os.clock() - started
        st.progress("Decompiling", obj, i, total, elapsed > 0 and i / elapsed or nil)
    end
    stat.decompileTime = os.clock() - started
    stat.rate = stat.decompileTime > 0 and total / stat.decompileTime or 0
    return cache
end

local actorcode = [[
local id, src = ...
local ch = get_comm_channel(id)
local ok, api = pcall(function()
    local fn, err = loadstring(src, "@LumenWorker")
    assert(fn, err)
    return fn()
end)
if not ok then
    ch:Fire("boot", false, tostring(api))
    return
end
ch.Event:Connect(function(kind, jid, obj)
    if kind ~= "job" then return end
    local good, out = pcall(function()
        return api:decompile(obj)
    end)
    if good and type(out) == "string" and out ~= "" then
        ch:Fire("done", jid, true, out)
    else
        ch:Fire("done", jid, false, tostring(out))
    end
end)
ch:Fire("boot", true, "")
]]

local function actors(lumen, list, opt, stat)
    if opt.Parallel == false then return nil, "disabled" end
    if #list < 48 then return nil, "too few scripts" end
    if type(run_on_actor) ~= "function" or type(create_comm_channel) ~= "function" or type(get_comm_channel) ~= "function" then
        return nil, "Potassium actor APIs unavailable"
    end
    if type(lumen._workerSource) ~= "function" then return nil, "worker source unavailable" end

    local want = tonumber(opt.MaxWorkers) or 4
    want = math.max(2, math.min(math.floor(want), 32, math.max(2, math.floor(#list / 24))))

    local pool = {}
    local owned = nil
    local ownok = pcall(function()
        local parent = game:GetService("ReplicatedStorage")
        owned = Instance.new("Folder")
        owned.Name = "__LumenWorkers_" .. tostring(math.floor(os.clock() * 1000))
        owned.Archivable = false
        owned.Parent = parent
        for i = 1, want do
            local a = Instance.new("Actor")
            a.Name = "Worker" .. tostring(i)
            a.Archivable = false
            a.Parent = owned
            pool[#pool + 1] = a
        end
    end)

    if not ownok or #pool < 2 then
        if owned then pcall(function() owned:Destroy() end) end
        owned = nil
        pool = {}
        if type(getactors) ~= "function" then return nil, "could not create worker Actors and getactors is unavailable" end
        local ok, existing = pcall(getactors)
        if not ok then return nil, "getactors failed: " .. tostring(existing) end
        if type(existing) ~= "table" or #existing < 2 then return nil, "fewer than 2 usable Actors" end
        pool = existing
        want = math.min(want, #pool)
    else
        task.wait()
    end

    local src = lumen:_workerSource()
    if type(src) ~= "string" or src == "" then
        if owned then pcall(function() owned:Destroy() end) end
        return nil, "empty worker source"
    end

    local ws = {}
    local q = {}
    local booted = 0
    local bootfail = 0

    for i = 1, want do
        local id, ch = create_comm_channel()
        local w = { id = id, ch = ch, actor = pool[i], ready = false, dead = false, busy = false, sent = 0 }
        w.con = ch.Event:Connect(function(kind, a, b, c)
            if kind == "boot" then
                if a then
                    if not w.ready then booted += 1 end
                    w.ready = true
                else
                    if not w.dead then bootfail += 1 end
                    w.dead = true
                    w.err = tostring(b)
                end
            elseif kind == "done" then
                q[#q + 1] = { w = w, jid = a, ok = b, out = c }
            end
        end)
        ws[#ws + 1] = w
        local rok, rerr = pcall(run_on_actor, w.actor, actorcode, id, src)
        if not rok then
            w.dead = true
            w.err = tostring(rerr)
            bootfail += 1
        end
    end

    local bt = os.clock()
    while booted + bootfail < #ws and os.clock() - bt < 8 do task.wait(0.01) end

    local live = {}
    for _, w in ipairs(ws) do
        if w.ready and not w.dead then live[#live + 1] = w end
    end
    if #live < 2 then
        local why = {}
        for _, w in ipairs(ws) do
            if w.err then why[#why + 1] = w.err end
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
        if owned then pcall(function() owned:Destroy() end) end
        return nil, "worker boot failed" .. (#why > 0 and (": " .. table.concat(why, " | ")) or "")
    end

    stat.parallel = #live
    stat.found = #list
    local cache = {}
    local nextjob = 1
    local done = 0
    local active = {}
    local started = os.clock()

    local function send(w)
        if w.dead or nextjob > #list then return end
        local jid = nextjob
        nextjob += 1
        w.busy = true
        w.sent = os.clock()
        w.jid = jid
        active[jid] = true
        w.ch:Fire("job", jid, list[jid])
    end

    for _, w in ipairs(live) do send(w) end

    while done < #list do
        while #q > 0 do
            local r = table.remove(q, 1)
            local w = r.w
            local jid = r.jid
            if active[jid] then
                active[jid] = nil
                done += 1
                w.busy = false
                local obj = list[jid]
                if r.ok and type(r.out) == "string" and r.out ~= "" then
                    cache[obj] = r.out
                    stat.good += 1
                else
                    local res = lumen:tryDecompile(obj, opt.Options)
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                        w.bad = (w.bad or 0) + 1
                        if w.bad >= 2 then w.dead = true end
                    else
                        fail(stat, obj, res.error or r.out)
                    end
                end
                local elapsed = os.clock() - started
                st.progress("Parallel decompile x" .. tostring(#live), obj, done, #list, elapsed > 0 and done / elapsed or nil)
                send(w)
            end
        end

        local now = os.clock()
        for _, w in ipairs(live) do
            if w.busy and now - w.sent > 60 then
                local jid = w.jid
                if active[jid] then
                    active[jid] = nil
                    w.dead = true
                    w.busy = false
                    local obj = list[jid]
                    local res = lumen:tryDecompile(obj, opt.Options)
                    done += 1
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                    else
                        fail(stat, obj, res.error or "parallel worker timeout")
                    end
                    local elapsed = os.clock() - started
                    st.progress("Parallel fallback", obj, done, #list, elapsed > 0 and done / elapsed or nil)
                end
            end
        end

        local alive = 0
        for _, w in ipairs(live) do if not w.dead then alive += 1 end end
        if alive == 0 and done < #list then
            for jid = 1, #list do
                if not cache[list[jid]] and active[jid] == nil and jid < nextjob then
                elseif jid >= nextjob then
                    local obj = list[jid]
                    local res = lumen:tryDecompile(obj, opt.Options)
                    done += 1
                    if res.success and type(res.source) == "string" and res.source ~= "" then
                        cache[obj] = res.source
                        stat.good += 1
                    else
                        fail(stat, obj, res.error)
                    end
                end
            end
            break
        end

        task.wait(0.005)
    end

    for _, w in ipairs(ws) do if w.con then pcall(function() w.con:Disconnect() end) end end
    if owned then pcall(function() owned:Destroy() end) end
    stat.decompileTime = os.clock() - started
    stat.rate = stat.decompileTime > 0 and #list / stat.decompileTime or 0
    return cache
end

local function writetree(root, list, cache, treeon, stat, made)
    local used = {}
    local total = #list
    local started = os.clock()
    local written = 0
    for i, obj in ipairs(list) do
        local src = cache[obj]
        if type(src) == "string" then
            local path = outpath(root, obj, not treeon, used, made)
            local ok, err = write(path, src)
            if ok then
                written += 1
            else
                stat.writeFailed += 1
                stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. tostring(err)
            end
        end
        st.progress("Writing source tree", obj, i, total)
    end
    stat.written = written
    stat.writeTime = os.clock() - started
end

local function summary(root, stat)
    local lines = {
        "LumenDecomp dump",
        "PlaceId: " .. tostring(game.PlaceId),
        "Scripts found: " .. tostring(stat.found),
        "Decompiled: " .. tostring(stat.good),
        "Failed/skipped: " .. tostring(stat.failed),
        "Source files written: " .. tostring(stat.written or 0),
        "Write failures: " .. tostring(stat.writeFailed),
        "Binary: " .. tostring(stat.binary),
        "Workers: " .. tostring(stat.parallel or 1),
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
    local stat = { found = 0, good = 0, failed = 0, written = 0, writeFailed = 0, binary = false, errors = {}, decompileTime = 0, writeTime = 0, rate = 0, parallel = 1 }
    local made = {}
    mkall(root, made)
    st.set("Starting", tostring(game.Name) .. " | " .. root)

    local list
    local cache
    if opt.Decompile and (opt.Tree or not opt.Binary) then
        list = scripts(opt.IgnoreCoreScripts == true)
        local pok, pout, preason = pcall(actors, lumen, list, opt, stat)
        if pok then
            cache = pout
            if not cache and preason and opt.Parallel ~= false then
                if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel unavailable: " .. tostring(preason) .. "\n") end
                warn("[LumenDecomp] parallel unavailable: " .. tostring(preason))
            end
        else
            if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel fallback: " .. tostring(pout) .. "\n") end
            warn("[LumenDecomp] parallel fallback: " .. tostring(pout))
        end
        if not cache then cache = serial(lumen, list, opt, stat) end
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
                IgnoreCoreScripts = opt.IgnoreCoreScripts == true,
                NilInstances = opt.NilInstances == true,
                RemovePlayerCharacters = opt.RemovePlayerCharacters == true,
                SavePlayers = opt.SavePlayers == true,
                MaxThreads = opt.MaxThreads or 8,
                DecompileIgnore = opt.IgnoreCoreScripts and { "Chat", "CoreGui", "CorePackages", "RobloxReplicatedStorage", "CoreScriptSyncService" } or opt.DecompileIgnore,
                ShowStatus = false,
            })
        end)
        stat.binary = ok
        if not ok then stat.errors[#stat.errors + 1] = "binary :: " .. tostring(err) end
    end

    summary(root, stat)
    if stat.good == 0 and stat.failed > 0 then
        st.done("FAILED - 0 decompiled, " .. tostring(stat.failed) .. " failed | " .. tostring(stat.errors[1] or "unknown failure"))
    else
        local mode = stat.parallel and stat.parallel > 1 and (" x" .. tostring(stat.parallel)) or ""
        st.done("Done - " .. tostring(stat.good) .. " decompiled, " .. tostring(stat.failed) .. " failed | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
    end
    return root, stat
end

function dump.auto(lumen, boot)
    local e = env.get()

    local function val(name)
        if type(boot) == "table" and boot[name] ~= nil then return boot[name] end
        local v = rawget(e, name)
        if v ~= nil then return v end
        if type(getfenv) == "function" then
            for level = 0, 8 do
                local ok, scope = pcall(getfenv, level)
                if ok and type(scope) == "table" then
                    v = rawget(scope, name)
                    if v ~= nil then return v end
                end
            end
        end
        return rawget(_G, name)
    end

    local binary = val("Binary") == true
    local decomp = val("Decompile") == true
    local treeon = val("Tree") == true
    local ignorecore = val("IgnoreCoreScripts") == true
    local parallel = val("Parallel")
    if parallel == nil then parallel = true else parallel = parallel == true end
    local maxworkers = tonumber(val("MaxWorkers")) or 4
    local flags = "Binary=" .. tostring(binary) .. " | Decompile=" .. tostring(decomp) .. " | Tree=" .. tostring(treeon) .. " | IgnoreCoreScripts=" .. tostring(ignorecore) .. " | Parallel=" .. tostring(parallel) .. " | MaxWorkers=" .. tostring(maxworkers)

    st.set("Loaded", "v" .. tostring(lumen.Version) .. " | " .. flags)
    print("[LumenDecomp] " .. flags)
    if not binary and not decomp and not treeon then
        task.delay(2, function() st.done("Loaded - idle | " .. flags) end)
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
            dump.run(lumen, { Binary = binary, Decompile = decomp, Tree = treeon, IgnoreCoreScripts = ignorecore, Parallel = parallel, MaxWorkers = maxworkers })
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
