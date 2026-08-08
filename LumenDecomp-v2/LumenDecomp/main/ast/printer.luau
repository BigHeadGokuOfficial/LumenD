local printast = {}

local function line(out, depth, s)
    out[#out + 1] = string.rep("    ", depth) .. s
end

local function block(out, b, depth)
    for _, node in ipairs(b.body) do
        if not node.dead then
            local k = node.kind
            if k == "raw" or k == "return" or k == "break" or k == "continue" then
                line(out, depth, node.text)
            elseif k == "if" then
                for i, branch in ipairs(node.branches) do
                    line(out, depth, (i == 1 and "if " or "elseif ") .. branch.cond .. " then")
                    block(out, branch.body, depth + 1)
                end
                if node.elsebody then
                    line(out, depth, "else")
                    block(out, node.elsebody, depth + 1)
                end
                line(out, depth, "end")
            elseif k == "while" then
                line(out, depth, "while " .. node.cond .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "repeat" then
                line(out, depth, "repeat")
                block(out, node.body, depth + 1)
                line(out, depth, "until " .. node.cond)
            elseif k == "for" then
                line(out, depth, node.head .. " do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "do" then
                line(out, depth, "do")
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            elseif k == "function" then
                if node.localfn then
                    line(out, depth, "local function " .. node.name .. "(" .. node.args .. ")")
                elseif node.assign then
                    line(out, depth, node.name .. " = function(" .. node.args .. ")")
                else
                    line(out, depth, "function " .. node.name .. "(" .. node.args .. ")")
                end
                block(out, node.body, depth + 1)
                line(out, depth, "end")
            end
        end
    end
end

function printast.run(root)
    local out = {}
    block(out, root, 0)
    return table.concat(out, "\n")
end

return printast
