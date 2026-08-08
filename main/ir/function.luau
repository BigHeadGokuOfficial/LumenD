local fn = {}
fn.__index = fn

function fn.new(proto, cfg, flow)
    return setmetatable({
        proto = proto,
        cfg = cfg,
        ssa = flow,
        vals = {},
        blocks = {},
        ops = {},
        bypc = {},
        phis = {},
        alias = {},
        usemap = {},
        inline = {},
        dead = {},
        const = {},
    }, fn)
end

function fn:resolve(id)
    if not id then return nil end
    local start = id
    local root = id
    local n = 0

    while self.alias[root] and self.alias[root] ~= root do
        root = self.alias[root]
        n += 1
        if n > 256 then break end
    end

    if root ~= start then
        local cur = start
        n = 0
        while self.alias[cur] and self.alias[cur] ~= root and n <= 256 do
            local nextid = self.alias[cur]
            self.alias[cur] = root
            cur = nextid
            n += 1
        end
    end

    return root
end

function fn:use(pc, reg)
    local uses = self.ssa.usesByPC[pc]
    return self:resolve(uses and uses[reg] or nil)
end

function fn:def(pc, reg)
    local defs = self.ssa.defsByPC[pc]
    return self:resolve(defs and defs[reg] or nil)
end

function fn:uses(id)
    id = self:resolve(id)
    return id and self.usemap[id] or nil
end

function fn:count(id)
    local uses = self:uses(id)
    return uses and #uses or 0
end

function fn:only(id)
    local uses = self:uses(id)
    return uses and #uses == 1 and uses[1] or nil
end

function fn:nameid(id)
    id = self:resolve(id)
    return id and ((self.family and self.family[id]) or id) or nil
end

function fn:reindex()
    local map = {}
    for pc, uses in pairs(self.ssa.usesByPC) do
        for reg, raw in pairs(uses) do
            local id = self:resolve(raw)
            if id then
                local list = map[id] or {}
                map[id] = list
                list[#list + 1] = { pc = pc, reg = reg, block = self.cfg.blockmap[pc] }
            end
        end
    end
    for bid, phis in pairs(self.phis) do
        for reg, p in pairs(phis) do
            if not self.dead[p.id] then
                local clean = {}
                for raw in pairs(p.inputs or {}) do
                    local id = self:resolve(raw)
                    if id and id ~= p.id then clean[id] = true end
                end
                p.inputs = clean
                for id in pairs(clean) do
                    local list = map[id] or {}
                    map[id] = list
                    list[#list + 1] = { phi = p.id, block = bid, reg = reg }
                end
            end
        end
    end
    self.usemap = map
    for id, v in pairs(self.vals) do v.uses = map[id] or {} end
end

return fn