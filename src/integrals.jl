# this should work for anything implementing the TermInterface

struct Integral
    iv
    from
    to
end
function (i::Integral)(x)
    integrate(x, i.iv, i.from, i.to)
end

SymbolicUtils.substitute(I::Integral, dict; fold=true) = Integral(substitute(I.iv, dict; fold), substitute(I.from, dict; fold), substitute(I.to, dict; fold))

Base.show(io::IO, i::Integral) = print(io, "∫d$(i.iv)[$(i.from) to $(i.to)]")

function occursin(f::FnCall, x)
    for a in f.args
        occursin(a, x) && return true
    end
    return f.op isa Integral && f.op.iv == x
end

isgen(p::Polyform) = !iscall(p)
function occursin(p::Polyform, x)
    if isgen(x)
        isgen(p) && x.p == p.p && return true
        invars(p, x.p) && return true
        p = docleanup(p)
        return any(occursin(fn, x) for fn in values(p.fns))
    else
        p == x && return true
        !iscall(p) && return false
        return any(occursin(a, x) for a in arguments(p))
    end
end

function occursin(p::RingElem, x::RingElem)
    p == x && return true
    !iscall(p) && return false
    return any(occursin(a, x) for a in arguments(p))
end

occursin(p::Number, x) = false
occursin(p::Symbol, x) = false
Base.rationalize(p::Polyform) = p

integrate(p, x, from, to) = integrate(p, x, Polyform(from), Polyform(to))
function integrate(p, x, from::Polyform, to::Polyform)
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
            return *(makeop(Integ, *(argswithx...)), argswithoutx...)
        end
        return *(Integ(only(argswithx)), argswithoutx...)
    elseif op == /
        nom, denom = arguments(p)
        if !hasx(denom)
            return Integ(nom) / denom
        end
    elseif op == +
        return sum(map(Integ, arguments(p)))
    elseif op isa Derivative
        if length(op.ivs) == 1 && x in op.ivs
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

    return makeop(Integral(x, from, to), p)
end
