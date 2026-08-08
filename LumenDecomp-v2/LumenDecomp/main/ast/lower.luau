local n = require("main.ast.nodes")

local build = {}
build.__index = build

local function add(body, node)
    body.body[#body.body + 1] = node
    return node
end

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

function build.new()
    local root = n.block()
    return setmetatable({ root = root, stack = { { kind = "root", body = root } } }, build)
end

function build:body()
    return self.stack[#self.stack].body
end

function build:add(node)
    return add(self:body(), node)
end

function build:last()
    local body = self:body().body
    return body[#body]
end

function build:emit(line)
    line = trim(line)

    local cond, act = line:match("^if%s+(.+)%s+then%s+(break)%s+end$")
    if not cond then cond, act = line:match("^if%s+(.+)%s+then%s+(continue)%s+end$") end
    if cond then
        local node = n.if_(cond)
        add(node.branches[1].body, n.term(act, act))
        return self:add(node)
    end

    cond = line:match("^if%s+(.+)%s+then$")
    if cond then
        local node = self:add(n.if_(cond))
        self.stack[#self.stack + 1] = { kind = "if", node = node, body = node.branches[1].body }
        return node
    end

    cond = line:match("^elseif%s+(.+)%s+then$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray elseif")
        local branch = { cond = cond, body = n.block() }
        top.node.branches[#top.node.branches + 1] = branch
        top.body = branch.body
        return top.node
    end

    if line == "else" then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "if", "LumenDecomp: stray else")
        top.node.elsebody = n.block()
        top.body = top.node.elsebody
        return top.node
    end

    cond = line:match("^while%s+(.+)%s+do$")
    if cond then
        local node = self:add(n.while_(cond))
        self.stack[#self.stack + 1] = { kind = "while", node = node, body = node.body }
        return node
    end

    if line == "repeat" then
        local node = self:add(n.repeat_())
        self.stack[#self.stack + 1] = { kind = "repeat", node = node, body = node.body }
        return node
    end

    cond = line:match("^until%s+(.+)$")
    if cond then
        local top = self.stack[#self.stack]
        assert(top and top.kind == "repeat", "LumenDecomp: stray until")
        top.node.cond = cond
        self.stack[#self.stack] = nil
        return top.node
    end

    local head = line:match("^(for%s+.+)%s+do$")
    if head then
        local node = self:add(n.for_(head))
        self.stack[#self.stack + 1] = { kind = "for", node = node, body = node.body }
        return node
    end

    if line == "do" then
        local node = self:add(n.do_())
        self.stack[#self.stack + 1] = { kind = "do", node = node, body = node.body }
        return node
    end

    local name, args = line:match("^local%s+function%s+([%w_]+)%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), true, false))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    name, args = line:match("^([%w_]+)%s*=%s*function%((.*)%)$")
    if name then
        local node = self:add(n.func(name, args, n.block(), false, true))
        self.stack[#self.stack + 1] = { kind = "function", node = node, body = node.body }
        return node
    end

    if line == "end" then
        local top = self.stack[#self.stack]
        assert(#self.stack > 1 and top.kind ~= "repeat", "LumenDecomp: stray end")
        self.stack[#self.stack] = nil
        return top.node
    end

    if line == "break" then return self:add(n.term("break", line)) end
    if line == "continue" then return self:add(n.term("continue", line)) end
    if line == "return" or line:match("^return%s") then return self:add(n.term("return", line)) end

    return self:add(n.raw(line))
end

function build:done()
    assert(#self.stack == 1, "LumenDecomp: AST builder has unclosed blocks")
    return self.root
end

return build
