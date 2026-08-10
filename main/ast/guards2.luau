local condition = require("main.ast.condition_utils")

local pass = {}

local function lastlive(block)
    for i = #(block and block.body or {}), 1, -1 do
        local node = block.body[i]
        if node and not node.dead then return node end
    end
end

local function terminates(block)
    local node = lastlive(block)
    if not node then return false end
    if node.kind == "return" or node.kind == "break" or node.kind == "continue" then
        return true
    end
    if node.kind == "if" and node.elsebody then
        for _, branch in ipairs(node.branches or {}) do
            if not terminates(branch.body) then return false end
        end
        return terminates(node.elsebody)
    end
    return false
end

local function declaresatroot(block)
    for _, node in ipairs(block.body or {}) do
        if not node.dead then
            if node.kind == "decl" then return true end
            if node.kind == "assign" and node.declare then return true end
            if node.kind == "function" and node.localfn then return true end
            if node.kind == "raw" and node.text and node.text:match("^local%s") then return true end
        end
    end
    return false
end

local function appendtail(out, body)
    if declaresatroot(body) then
        out[#out + 1] = { kind = "do", body = body }
    else
        for _, node in ipairs(body.body or {}) do out[#out + 1] = node end
    end
end

local function walk(block)
    local out = {}
    for _, node in ipairs(block.body or {}) do
        if node.kind == "if" then
            for _, branch in ipairs(node.branches or {}) do walk(branch.body) end
            if node.elsebody then walk(node.elsebody) end

            if #node.branches == 1 and node.elsebody then
                local branch = node.branches[1]
                local thenends = terminates(branch.body)
                local elseends = terminates(node.elsebody)

                if thenends and not elseends then
                    local tail = node.elsebody
                    node.elsebody = nil
                    out[#out + 1] = node
                    appendtail(out, tail)
                elseif elseends and not thenends then
                    local tail = branch.body
                    local guard = {
                        kind = "if",
                        branches = {
                            {
                                cond = condition.negate(branch.cond),
                                body = node.elsebody,
                            },
                        },
                        elsebody = nil,
                    }
                    out[#out + 1] = guard
                    appendtail(out, tail)
                else
                    out[#out + 1] = node
                end
            else
                out[#out + 1] = node
            end
        else
            if node.body then walk(node.body) end
            out[#out + 1] = node
        end
    end
    block.body = out
end

function pass.run(root)
    walk(root)
    return root
end

return pass
