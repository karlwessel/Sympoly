# this should work for anything implementing the TermInterface

struct Integral
    iv
    from
    to
end
function (i::Integral)(x)
    integrate(x, i.iv, i.from, i.to)
end

Base.show(io::IO, i::Integral) = print(io, "∫d$(i.iv)[$(i.from) to $(i.to)]")

function occursin(f::FnCall, x)
    for a in f.args
        occursin(a, x) && return true
    end
    return f.op.op isa Integral && f.op.op.iv == x
end

isgen(p::Polyform) = !iscall(p)
function occursin(p::Polyform, x)
    if isgen(x)
        isgen(p) && x.p == p.p && return true
        invars(p, x.p) && return true
        p = docleanup(p)
        for fn in values(p.fns)
            occursin(fn, x) && return true
        end
        return false
    else
        p == x && return true

        !iscall(p) && return false
        for a in arguments(p)
            occursin(a, x) && return true
        end
        return false
    end
end

occursin(p::Number, x) = p == x
Base.rationalize(p::Polyform) = p

function integrate(p, x, from, to)
    hasx(p) = occursin(p, x)
    Integ = Integral(x, from, to)
    !hasx(p) && return p*(to - from)
    isgen(p) && isgen(x) && p.p == x.p && return 1//2*(to^2 - from^2)

    intmap = Dict([cos => sin,
        sin => x -> -cos(x),
        cospi => x -> sinpi(x) / pi,
        sinpi => x -> -cospi(x) / pi])

    op = operation(p)
    if op == *
        args = arguments(p)
        withxidx = hasx.(args)
        argswithx = args[withxidx]
        argswithoutx = args[(.!)(withxidx)]
        if length(argswithx) > 1
            return *(makeop(Integ, *(argswithx...); nofn=true), argswithoutx...)
        end
        return *(Integ(only(argswithx)), argswithoutx...)
    elseif op == /
        nom, denom = arguments(p)
        if !hasx(denom)
            return Integ(nom) / denom
        end
    elseif op == +
        return sum(map(Integ, arguments(p)))
    elseif op isa Fn && op.op isa Derivative
        if length(op.op.ivs) == 1 && x in op.op.ivs
            arg = only(arguments(p))
            return substitute(arg, x => to) - substitute(arg, x => from)
        end
    elseif haskey(intmap, op)
        y = only(arguments(p))
        intop = intmap[op]
        dy = derive(y, x)
        if !hasx(dy)
            r = intop(substitute(y, x => to)) - intop(substitute(y, x => from))
            return tonumber(r/dy)
        end
    end

    return makeop(Integral(x, from, to), p; nofn=true)
end
