local st = {}

local gui
local text
local dead = false
local lastui = 0
local lastcon = 0

local function parent()
    if type(gethui) == "function" then
        local ok, out = pcall(gethui)
        if ok and out then return out end
    end

    local ok, out = pcall(function()
        return game:GetService("CoreGui")
    end)
    if ok then return out end
end

local function make()
    if gui and gui.Parent then return true end

    local p = parent()
    if not p then return false end

    local ok = pcall(function()
        gui = Instance.new("ScreenGui")
        gui.Name = "LumenStatus"
        gui.ResetOnSpawn = false
        gui.IgnoreGuiInset = true
        gui.DisplayOrder = 2147483647

        local box = Instance.new("Frame")
        box.Name = "Box"
        box.AnchorPoint = Vector2.new(0.5, 0)
        box.Position = UDim2.new(0.5, 0, 0, 12)
        box.Size = UDim2.new(0, 760, 0, 54)
        box.BackgroundColor3 = Color3.fromRGB(14, 14, 17)
        box.BackgroundTransparency = 0.08
        box.BorderSizePixel = 0
        box.Parent = gui

        local corner = Instance.new("UICorner")
        corner.CornerRadius = UDim.new(0, 8)
        corner.Parent = box

        text = Instance.new("TextLabel")
        text.Name = "Text"
        text.BackgroundTransparency = 1
        text.Position = UDim2.new(0, 14, 0, 5)
        text.Size = UDim2.new(1, -28, 1, -10)
        text.Font = Enum.Font.Code
        text.TextColor3 = Color3.fromRGB(245, 245, 245)
        text.TextSize = 15
        text.TextXAlignment = Enum.TextXAlignment.Left
        text.TextYAlignment = Enum.TextYAlignment.Center
        text.TextWrapped = true
        text.Text = "LumenDecomp"
        text.Parent = box

        gui.Parent = p
    end)

    return ok
end

function st.path(obj)
    if not obj then return "" end
    local ok, out = pcall(function()
        return obj:GetFullName()
    end)
    return ok and out or tostring(obj)
end

local function msg(stage, obj, done, total, rate)
    local path = type(obj) == "string" and obj or st.path(obj)
    local count = ""
    if done and total then
        count = " [" .. tostring(done) .. "/" .. tostring(total) .. "]"
    end
    if rate then
        count = count .. " " .. string.format("%.1f/s", rate)
    end
    local out = "LumenDecomp — " .. tostring(stage) .. count
    if path ~= "" then out = out .. "\n" .. path end
    return out
end

local function show(out, console)
    if dead then return end
    if make() and text then text.Text = out end
    if console and type(rconsoleprint) == "function" then
        pcall(rconsoleprint, out .. "\n")
    end
end

function st.set(stage, obj, done, total)
    local out = msg(stage, obj, done, total)
    show(out, true)
    lastui = os.clock()
    lastcon = lastui
end

function st.progress(stage, obj, done, total, rate)
    if dead then return end
    local now = os.clock()
    if done ~= total and now - lastui < 0.075 then return end
    local out = msg(stage, obj, done, total, rate)
    local con = done == total or now - lastcon >= 0.5
    show(out, con)
    lastui = now
    if con then lastcon = now end
end

function st.done(msgtext)
    st.set(msgtext or "Done")
    if gui then
        task.delay(5, function()
            if gui then pcall(function() gui:Destroy() end) end
            gui = nil
            text = nil
        end)
    end
end

function st.kill()
    dead = true
    if gui then pcall(function() gui:Destroy() end) end
    gui = nil
    text = nil
end

return st
