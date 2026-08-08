local n = {}

function n.block()
    return { kind = "block", body = {} }
end

function n.raw(s)
    return { kind = "raw", text = s }
end

function n.if_(cond)
    return { kind = "if", branches = { { cond = cond, body = n.block() } }, elsebody = nil }
end

function n.while_(cond)
    return { kind = "while", cond = cond, body = n.block() }
end

function n.repeat_()
    return { kind = "repeat", cond = "true", body = n.block() }
end

function n.for_(head)
    return { kind = "for", head = head, body = n.block() }
end

function n.do_()
    return { kind = "do", body = n.block() }
end

function n.func(name, args, body, localfn, assign)
    return { kind = "function", name = name, args = args, body = body or n.block(), localfn = localfn == true, assign = assign == true }
end

function n.term(kind, text)
    return { kind = kind, text = text }
end

return n