
local env = require("main.runtime.environment")
local st = require("main.runtime.status")
local coref = require("main.runtime.core")
local bc = require("main.runtime.bytecode")
local tree = require("main.tree")
local config = require("main.config")

local dump = {}

local function accept(stat, source)
    stat.good += 1
    local status = source:match('^local __lumenmeta = "LumenV4 status=([A-Z_]+)')
    if status == "LOSSLESS_FALLBACK" or status == "VM_FALLBACK" then
        stat.fallback += 1
    elseif status == "STRUCTURED" then
        stat.structured += 1
    else
        stat.unknown += 1
    end
    local reachable, covered = source:match("reachable=(%d+) covered=(%d+)")
    stat.reachable += tonumber(reachable) or 0
    stat.covered += tonumber(covered) or 0
    local sb, fb = source:match("structuredBlocks=(%d+) fallbackBlocks=(%d+)")
    stat.sblocks += tonumber(sb) or 0
    stat.fblocks += tonumber(fb) or 0
    stat.phis += tonumber(source:match("phis=(%d+)")) or 0
    stat.packs += tonumber(source:match("packs=(%d+)")) or 0
    stat.cells += tonumber(source:match("cells=(%d+)")) or 0
    stat.objects += tonumber(source:match("objects=(%d+)")) or 0
    stat.escaped += tonumber(source:match("escapedObjects=(%d+)")) or 0
    stat.irreducible += tonumber(source:match("irreducible=(%d+)")) or 0
    local bv = tonumber(source:match("bytecodeVersion=(%d+)"))
    if bv then stat.versions[bv] = (stat.versions[bv] or 0) + 1 end
    if source:find("parser=true", 1, true) then stat.syntax += 1 end
end

local function rootdir()
    return "LumenDecomp/" .. tostring(game.PlaceId or 0) .. "/dump_" .. tostring(os.time())
end

local function write(path, data)
    if type(writefile) ~= "function" then return false, "executor does not expose writefile()" end
    local ok, err = pcall(writefile, path, data)
    return ok, err
end

local function decompfail(stat, cache, obj, err)
    err = tostring(err)
    stat.failed += 1
    if err:find("LumenV4: PARTIAL", 1, true) then stat.partial += 1
    elseif err:find("LumenV4: INVALID", 1, true) then stat.invalid += 1
    elseif err:find("LumenV4: UNSUPPORTED", 1, true) then stat.unsupported += 1
    else stat.other += 1 end
    cache[obj] = { success = false, error = err }
    local line = st.path(obj) .. " :: " .. err
    stat.errors[#stat.errors + 1] = line
    if stat.failed <= 5 then
        if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] FAIL " .. line .. "\n") end
        warn("[LumenDecomp] FAIL " .. line)
    end
end

local function unavailable(stat, cache, obj, err)
    err = tostring(err)
    stat.unavailable += 1
    if obj.ClassName == "Script" then stat.serverUnavailable += 1 end
    cache[obj] = { success = false, unavailable = true, error = err }
    local line = st.path(obj) .. " :: " .. err
    stat.unavailableErrors[#stat.unavailableErrors + 1] = line
end

local function acquire(list, stat, opt)
    local jobs = {}
    local cache = {}
    local started = os.clock()
    local slice = started
    local total = #list
    local batch = tonumber(opt.AcquireBatch)
    if not batch then
        if total >= 500 then batch = 3
        elseif total >= 200 then batch = 4
        elseif total >= 80 then batch = 6
        else batch = 12 end
    end
    batch = math.max(1, math.floor(batch))
    local budget = math.max(0.001, (tonumber(opt.AcquireBudgetMs) or 3) / 1000)
    stat.found = total
    stat.acquireBatch = batch
    stat.acquireBudgetMs = budget * 1000

    for i, obj in ipairs(list) do
        local ok, raw = bc.try(obj)
        if ok then
            if typeof(raw) == "buffer" then raw = buffer.tostring(raw) end
            jobs[#jobs + 1] = { obj = obj, raw = raw }
        else
            unavailable(stat, cache, obj, raw)
        end
        st.progress("Acquiring bytecode", obj, i, total)
        local now = os.clock()
        if i < total and (i % batch == 0 or now - slice >= budget) then
            stat.acquireYields += 1
            task.wait()
            slice = os.clock()
        end
    end

    stat.available = #jobs
    stat.acquireTime = os.clock() - started
    return jobs, cache
end

local function decopt(opt)
    local out = {}
    if type(opt.Options) == "table" then
        for k, v in pairs(opt.Options) do out[k] = v end
    end
    return out
end

local function warm(lumen, stat)
    local t = os.clock()
    local ok, err = pcall(function() return lumen:warm() end)
    stat.warmTime += os.clock() - t
    if not ok then return false, tostring(err) end
    return true
end

local function serial(lumen, jobs, opt, stat, cache, label)
    local ok, err = warm(lumen, stat)
    if not ok then
        for _, job in ipairs(jobs) do decompfail(stat, cache, job.obj, err) end
        stat.decompileTime = 0
        stat.rate = 0
        return cache
    end

    local started = os.clock()
    local cfg = decopt(opt)
    local total = #jobs
    local slice = os.clock()
    local budget = math.max(0.001, (tonumber(opt.DecompileBudgetMs) or 8) / 1000)
    for i, job in ipairs(jobs) do
        local res = lumen:tryDecompileBytecode(job.raw, cfg)
        if res.success and type(res.source) == "string" and res.source ~= "" then
            cache[job.obj] = res.source
            accept(stat, res.source)
        else
            decompfail(stat, cache, job.obj, res.error)
        end
        local elapsed = os.clock() - started
        st.progress(label or "Decompiling", job.obj, i, total, elapsed > 0 and i / elapsed or nil)
        if i < total and os.clock() - slice >= budget then
            task.wait()
            slice = os.clock()
        end
    end
    stat.decompileTime += os.clock() - started
    stat.rate = stat.decompileTime > 0 and stat.available / stat.decompileTime or 0
    return cache
end

local actorcode = [[
local id, src, vendor, smart, funcs, guards, fold, conds, blocks = ...
local ch = get_comm_channel(id)
local genv = type(getgenv) == "function" and getgenv() or _G
local okv, v = pcall(function()
    if type(vendor) ~= "string" or vendor == "" then return nil end
    local fn, err = loadstring(vendor, "@LumenIridiumVendor")
    assert(fn, err)
    return fn()
end)
if okv and type(v) == "table" then
    genv.__LUMEN_IRIDIUM_VENDOR = v
    _G.__LUMEN_IRIDIUM_VENDOR = v
end
local ok, api = pcall(function()
    local fn, err = loadstring(src, "@LumenWorker")
    assert(fn, err)
    return fn()
end)
if not ok then
    ch:Fire("boot", false, tostring(api))
    return
end
local wok, werr = pcall(function() return api:warm() end)
if not wok then
    ch:Fire("boot", false, tostring(werr))
    return
end
genv.__LUMEN_IRIDIUM_VENDOR = nil
_G.__LUMEN_IRIDIUM_VENDOR = nil
local dec = {
    smartnames = smart,
    functions = funcs,
    guards = guards,
    fold = fold,
    conditions = conds,
    doblocks = blocks,
}
local con
con = ch.Event:Connect(function(kind, jid, raw)
    if kind == "stop" then
        if con then con:Disconnect() end
        return
    end
    if kind ~= "job" then return end
    local good, out = pcall(function() return api:decompileBytecode(raw, dec) end)
    if good and type(out) == "string" and out ~= "" then
        ch:Fire("done", jid, true, out)
    else
        ch:Fire("done", jid, false, tostring(out))
    end
end)
ch:Fire("boot", true, "")
]]

local function getpool()
    local pool = {}
    if type(getactors) ~= "function" then return pool end
    local ok, list = pcall(getactors)
    if not ok or type(list) ~= "table" then return pool end
    for _, a in ipairs(list) do
        if typeof(a) == "Instance" and a:IsA("Actor") then pool[#pool + 1] = a end
    end
    return pool
end

local function actors(lumen, jobs, opt, stat, cache)
    if opt.Parallel == false then return nil, "disabled" end
    if #jobs < 12 then return nil, "small corpus fast path" end
    if type(run_on_actor) ~= "function" or type(create_comm_channel) ~= "function" or type(get_comm_channel) ~= "function" then
        return nil, "Potassium actor APIs unavailable"
    end
    if type(lumen._workerSource) ~= "function" or type(lumen._iridiumPack) ~= "function" then
        return nil, "worker source unavailable"
    end

    local max = tonumber(opt.MaxWorkers) or 4
    max = math.max(2, math.min(math.floor(max), 32))
    local useful = math.max(2, math.floor(#jobs / 4))
    local want = math.min(max, 16, useful)

    local bootstart = os.clock()
    local vendor, verr = lumen:_iridiumPack()
    if type(vendor) ~= "string" then return nil, "Iridium prefetch failed: " .. tostring(verr) end
    stat.warmTime += os.clock() - bootstart

    local pool = getpool()
    if #pool < 2 then return nil, "fewer than 2 executor-reported Actors" end

    local src = lumen:_workerSource()
    if type(src) ~= "string" or src == "" then return nil, "empty worker source" end

    local ws = {}
    local live = {}
    local dc = config(decopt(opt))
    local q = {}
    local qhead = 1
    local qtail = 0
    local why = {}

    for _, actor in ipairs(pool) do
        if #live >= want then break end
        local id, ch = create_comm_channel()
        local w = { id = id, ch = ch, actor = actor, ready = false, dead = false, busy = false, sent = 0 }
        w.con = ch.Event:Connect(function(kind, a, b, c)
            if kind == "boot" then
                if a then w.ready = true else w.dead = true; w.err = tostring(b) end
            elseif kind == "done" then
                qtail += 1
                q[qtail] = { w = w, jid = a, ok = b, out = c }
            end
        end)
        ws[#ws + 1] = w
        local rok, rerr = pcall(run_on_actor, actor, actorcode, id, src, vendor, dc.smartnames ~= false, dc.functions ~= false, dc.guards ~= false, dc.fold ~= false, dc.conditions ~= false, dc.doblocks or 0)
        if not rok then
            w.dead = true
            w.err = tostring(rerr)
        else
            local bt = os.clock()
            while not w.ready and not w.dead and os.clock() - bt < 3 do task.wait(0.01) end
            if not w.ready then
                w.dead = true
                w.err = w.err or "worker boot timeout"
            end
        end
        if w.ready and not w.dead then
            live[#live + 1] = w
            task.wait()
        else
            why[#why + 1] = w.err or "unusable Actor"
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
    end

    stat.parallelBootTime = os.clock() - bootstart
    if #live < 2 then
        for _, w in ipairs(ws) do
            if w.ready then pcall(function() w.ch:Fire("stop") end) end
            if w.con then pcall(function() w.con:Disconnect() end) end
        end
        return nil, "worker boot failed" .. (#why > 0 and (": " .. table.concat(why, " | ")) or "")
    end

    stat.parallel = #live
    local nextjob = 1
    local done = 0
    local active = {}
    local retry = {}
    local started = os.clock()

    local function send(w)
        if w.dead or nextjob > #jobs then return end
        local jid = nextjob
        nextjob += 1
        w.busy = true
        w.sent = os.clock()
        w.jid = jid
        active[jid] = true
        w.ch:Fire("job", jid, jobs[jid].raw)
    end

    for _, w in ipairs(live) do send(w) end

    while done < #jobs do
        while qhead <= qtail do
            local r = q[qhead]
            q[qhead] = nil
            qhead += 1
            local w = r.w
            local jid = r.jid
            if active[jid] then
                active[jid] = nil
                done += 1
                w.busy = false
                local job = jobs[jid]
                if r.ok and type(r.out) == "string" and r.out ~= "" then
                    cache[job.obj] = r.out
                    accept(stat, r.out)
                else
                    retry[#retry + 1] = job
                end
                local elapsed = os.clock() - started
                st.progress("Parallel decompile x" .. tostring(#live), job.obj, done, #jobs, elapsed > 0 and done / elapsed or nil)
                send(w)
            end
        end

        local now = os.clock()
        for _, w in ipairs(live) do
            if w.busy and now - w.sent > 45 then
                local jid = w.jid
                if active[jid] then
                    active[jid] = nil
                    w.dead = true
                    w.busy = false
                    done += 1
                    retry[#retry + 1] = jobs[jid]
                end
            end
        end

        local alive = 0
        for _, w in ipairs(live) do if not w.dead then alive += 1 end end
        if alive == 0 then
            for jid = nextjob, #jobs do retry[#retry + 1] = jobs[jid] end
            done = #jobs
            break
        end
        task.wait(0.002)
    end

    for _, w in ipairs(ws) do
        pcall(function() w.ch:Fire("stop") end)
        if w.con then pcall(function() w.con:Disconnect() end) end
    end
    task.wait()

    stat.decompileTime += os.clock() - started

    if #retry > 0 then
        local wok, werr = warm(lumen, stat)
        if not wok then
            for _, job in ipairs(retry) do decompfail(stat, cache, job.obj, werr) end
        else
            local cfg = decopt(opt)
            local rs = os.clock()
            for i, job in ipairs(retry) do
                local res = lumen:tryDecompileBytecode(job.raw, cfg)
                if res.success and type(res.source) == "string" and res.source ~= "" then
                    cache[job.obj] = res.source
                    accept(stat, res.source)
                else
                    decompfail(stat, cache, job.obj, res.error)
                end
                st.progress("Retrying locally", job.obj, i, #retry)
            end
            stat.decompileTime += os.clock() - rs
        end
    end

    stat.rate = stat.decompileTime > 0 and stat.available / stat.decompileTime or 0
    return cache
end

local function writetree(root, list, cache, treeon, stat, made, opt)
    local ctx = tree.new(root, made, opt.MaxPathLength or 240, list)
    local started = os.clock()
    local written = 0
    local source = 0
    local placeholders = 0
    local slice = os.clock()
    local budget = math.max(0.001, (tonumber(opt.WriteBudgetMs) or 8) / 1000)

    for i, obj in ipairs(list) do
        local v = cache[obj]
        local body
        local state
        if type(v) == "string" then
            body = v
            state = "decompiled"
            source += 1
        elseif type(v) == "table" then
            body = tree.placeholder(obj, v)
            state = v.unavailable and "unavailable" or "failed"
            placeholders += 1
        else
            body = tree.placeholder(obj, { error = "no decompile result" })
            state = "missing"
            placeholders += 1
        end

        local path = tree.path(ctx, obj, treeon)
        local ok, err = write(path, body)
        if ok then
            written += 1
        else
            stat.writeFailed += 1
            stat.errors[#stat.errors + 1] = st.path(obj) .. " :: " .. tostring(err)
            state = "write-failed"
        end
        tree.record(ctx, obj, path, state)
        st.progress("Writing source tree", obj, i, #list)
        if i < #list and os.clock() - slice >= budget then
            task.wait()
            slice = os.clock()
        end
    end

    local mok, merr = write(root .. "/tree-map.tsv", tree.map(ctx))
    if not mok then
        stat.writeFailed += 1
        stat.errors[#stat.errors + 1] = "tree-map.tsv :: " .. tostring(merr)
    end

    stat.written = written
    stat.sourceWritten = source
    stat.placeholderWritten = placeholders
    stat.writeTime = os.clock() - started
end

local function summary(root, stat)
    local lines = {
        "LumenDecomp dump",
        "PlaceId: " .. tostring(game.PlaceId),
        "Script instances found: " .. tostring(stat.found),
        "Bytecode available: " .. tostring(stat.available),
        "Accepted source (syntax + origin coverage): " .. tostring(stat.good),
        "Structured accepted: " .. tostring(stat.structured),
        "Lossless/VM fallback accepted: " .. tostring(stat.fallback),
        "Partial: " .. tostring(stat.partial),
        "Invalid output: " .. tostring(stat.invalid),
        "Unsupported: " .. tostring(stat.unsupported),
        "Other failures: " .. tostring(stat.other),
        "Syntax-valid source: " .. tostring(stat.syntax) .. "/" .. tostring(stat.good),
        "Reachable instruction coverage: " .. (stat.reachable > 0 and string.format("%.2f%%", stat.covered * 100 / stat.reachable) or "100.00%"),
        "Structured blocks: " .. tostring(stat.sblocks),
        "Fallback blocks: " .. tostring(stat.fblocks),
        "Phi nodes: " .. tostring(stat.phis),
        "ValuePack producers: " .. tostring(stat.packs),
        "Captured cells: " .. tostring(stat.cells),
        "Tracked heap objects: " .. tostring(stat.objects),
        "Escaped heap objects: " .. tostring(stat.escaped),
        "Irreducible accepted functions: " .. tostring(stat.irreducible),
        "Decompile failures: " .. tostring(stat.failed),
        "Bytecode unavailable: " .. tostring(stat.unavailable),
        "Server Script unavailable: " .. tostring(stat.serverUnavailable),
        "Tree files written: " .. tostring(stat.written or 0),
        "Decompiled source files: " .. tostring(stat.sourceWritten or 0),
        "Placeholder files: " .. tostring(stat.placeholderWritten or 0),
        "Tree scan failures: " .. tostring(stat.scanFailed or 0),
        "Write failures: " .. tostring(stat.writeFailed),
        "Binary: " .. tostring(stat.binary),
        "Workers: " .. tostring(stat.parallel or 1),
        "SmartVariableRenamer: " .. tostring(stat.decompiler and stat.decompiler.smartnames ~= false),
        "FunctionDeclarations: " .. tostring(stat.decompiler and stat.decompiler.functions ~= false),
        "GuardClauses: " .. tostring(stat.decompiler and stat.decompiler.guards ~= false),
        "ConstantFolding: " .. tostring(stat.decompiler and stat.decompiler.fold ~= false),
        "ConditionalStructurer: " .. tostring(stat.decompiler and stat.decompiler.conditions ~= false),
        "DoBlockInsertionThreshold: " .. tostring(stat.decompiler and stat.decompiler.doblocks or 0),
        "Acquire seconds: " .. string.format("%.3f", stat.acquireTime or 0),
        "Acquire batch: " .. tostring(stat.acquireBatch or 0),
        "Acquire budget ms: " .. string.format("%.2f", stat.acquireBudgetMs or 0),
        "Acquire yields: " .. tostring(stat.acquireYields or 0),
        "Warmup seconds: " .. string.format("%.3f", stat.warmTime or 0),
        "Worker boot seconds: " .. string.format("%.3f", stat.parallelBootTime or 0),
        "Reconstruct seconds: " .. string.format("%.3f", stat.decompileTime or 0),
        "Reconstruct rate: " .. string.format("%.2f scripts/s", stat.rate or 0),
        "Write seconds: " .. string.format("%.3f", stat.writeTime or 0),
        "Total seconds: " .. string.format("%.3f", stat.totalTime or 0),
        "",
    }
    if #stat.errors > 0 then
        lines[#lines + 1] = "Decompile/write errors:"
        for _, e in ipairs(stat.errors) do lines[#lines + 1] = e end
        lines[#lines + 1] = ""
    end
    if #stat.unavailableErrors > 0 then
        lines[#lines + 1] = "Unavailable bytecode:"
        for _, e in ipairs(stat.unavailableErrors) do lines[#lines + 1] = e end
    end
    write(root .. "/summary.txt", table.concat(lines, "\n"))
end

function dump.run(lumen, opt)
    opt = opt or {}
    local totalstart = os.clock()
    local root = opt.Root or rootdir()
    local stat = {
        found = 0,
        available = 0,
        good = 0,
        structured = 0,
        fallback = 0,
        unknown = 0,
        partial = 0,
        invalid = 0,
        unsupported = 0,
        other = 0,
        syntax = 0,
        reachable = 0,
        covered = 0,
        sblocks = 0,
        fblocks = 0,
        phis = 0,
        packs = 0,
        cells = 0,
        objects = 0,
        escaped = 0,
        irreducible = 0,
        versions = {},
        failed = 0,
        unavailable = 0,
        serverUnavailable = 0,
        written = 0,
        sourceWritten = 0,
        placeholderWritten = 0,
        scanFailed = 0,
        writeFailed = 0,
        binary = false,
        errors = {},
        unavailableErrors = {},
        acquireTime = 0,
        acquireBatch = 0,
        acquireBudgetMs = 0,
        acquireYields = 0,
        warmTime = 0,
        parallelBootTime = 0,
        decompileTime = 0,
        writeTime = 0,
        totalTime = 0,
        rate = 0,
        parallel = 1,
        decompiler = config(decopt(opt)),
    }
    local made = {}
    tree.mkall(root, made)
    st.set("Starting", tostring(game.Name) .. " | " .. root)

    local list
    local cache
    if opt.Decompile and (opt.Tree or not opt.Binary) then
        local scanerr
        list, scanerr = tree.scan(opt.IgnoreCoreScripts == true, coref)
        stat.scanFailed = #scanerr
        for _, e in ipairs(scanerr) do stat.errors[#stat.errors + 1] = "scan :: " .. tostring(e) end
        local jobs
        jobs, cache = acquire(list, stat, opt)

        if #jobs > 0 then
            local pok, pout, preason = pcall(actors, lumen, jobs, opt, stat, cache)
            if pok then
                if pout then
                    cache = pout
                elseif preason and opt.Parallel ~= false then
                    if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel: " .. tostring(preason) .. "\n") end
                end
            else
                if type(rconsoleprint) == "function" then pcall(rconsoleprint, "[LumenDecomp] parallel fallback: " .. tostring(pout) .. "\n") end
                warn("[LumenDecomp] parallel fallback: " .. tostring(pout))
            end
            if stat.good + stat.failed < #jobs then
                local pending = {}
                for _, job in ipairs(jobs) do
                    if cache[job.obj] == nil then pending[#pending + 1] = job end
                end
                serial(lumen, pending, opt, stat, cache, "Decompiling")
            end
        end

        writetree(root, list, cache, opt.Tree, stat, made, opt)
    end

    if opt.Binary then
        st.set("Saving binary", cache and "reusing source/availability cache" or tostring(game.Name))
        task.wait()
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
                MaxThreads = opt.MaxThreads or 3,
                DecompileIgnore = opt.IgnoreCoreScripts and { "Chat", "CoreGui", "CorePackages", "RobloxReplicatedStorage", "CoreScriptSyncService" } or opt.DecompileIgnore,
                ShowStatus = false,
            })
        end)
        stat.binary = ok
        if not ok then stat.errors[#stat.errors + 1] = "binary :: " .. tostring(err) end
    end

    stat.totalTime = os.clock() - totalstart
    summary(root, stat)
    local mode = stat.parallel and stat.parallel > 1 and (" x" .. tostring(stat.parallel)) or ""
    if stat.failed > 0 then
        st.done("Done - " .. tostring(stat.good) .. " decompiled, " .. tostring(stat.failed) .. " failed, " .. tostring(stat.unavailable) .. " unavailable | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
    else
        st.done("Done - " .. tostring(stat.good) .. " decompiled, 0 failed, " .. tostring(stat.unavailable) .. " unavailable | " .. string.format("%.1f/s", stat.rate or 0) .. mode)
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
    local maxthreads = tonumber(val("MaxThreads")) or 3
    maxthreads = math.max(1, math.min(math.floor(maxthreads), 8))
    local maxpath = tonumber(val("MaxPathLength")) or 240
    local acquirebatch = tonumber(val("AcquireBatch"))
    local acquirebudget = tonumber(val("AcquireBudgetMs")) or 3
    local decompilebudget = tonumber(val("DecompileBudgetMs")) or 8
    local writebudget = tonumber(val("WriteBudgetMs")) or 8
    local dopt = val("DecompilerOptions")
    if type(dopt) ~= "table" then dopt = {} end
    local names = { "SmartVariableRenamer", "FunctionDeclarations", "GuardClauses", "ConstantFolding", "ConditionalStructurer", "DoBlockInsertionThreshold" }
    for _, name in ipairs(names) do
        local v = val(name)
        if v ~= nil then dopt[name] = v end
    end
    local flags = "Binary=" .. tostring(binary) .. " | Decompile=" .. tostring(decomp) .. " | Tree=" .. tostring(treeon) .. " | IgnoreCoreScripts=" .. tostring(ignorecore) .. " | Parallel=" .. tostring(parallel) .. " | MaxWorkers=" .. tostring(maxworkers) .. " | MaxThreads=" .. tostring(maxthreads)

    st.set("Loaded", "v" .. tostring(lumen.Version) .. " | " .. flags)
    print("[LumenDecomp] " .. flags)
    local dc = config(dopt)
    print("[LumenDecomp] SmartVariableRenamer=" .. tostring(dc.smartnames ~= false) .. " | FunctionDeclarations=" .. tostring(dc.functions ~= false) .. " | GuardClauses=" .. tostring(dc.guards ~= false) .. " | ConstantFolding=" .. tostring(dc.fold ~= false) .. " | ConditionalStructurer=" .. tostring(dc.conditions ~= false) .. " | DoBlockInsertionThreshold=" .. tostring(dc.doblocks or 0))
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
            dump.run(lumen, { Binary = binary, Decompile = decomp, Tree = treeon, IgnoreCoreScripts = ignorecore, Parallel = parallel, MaxWorkers = maxworkers, MaxThreads = maxthreads, MaxPathLength = maxpath, AcquireBatch = acquirebatch, AcquireBudgetMs = acquirebudget, DecompileBudgetMs = decompilebudget, WriteBudgetMs = writebudget, Options = dopt })
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
