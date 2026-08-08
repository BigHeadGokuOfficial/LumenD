local pass = {}

function pass.run(ir)
    ir.regions = {
        loops = ir.cfg.loops,
        ipdom = ir.cfg.ipdom,
        postdom = ir.cfg.postdom,
    }
    return ir
end

return pass
