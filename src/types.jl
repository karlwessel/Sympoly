R = universal_polynomial_ring(QQ)

struct Polyform <: Base.Real
    p
    denom
    fns
end

Polyform(x) = Polyform(x, one(x), Dict([]))
Polyform(x::AbstractFloat) = Polyform(tonumber(x))

function Polyform(x::Symbol)
    sx = gen(R, x)
    Polyform(sx, one(sx), Dict([]))
end

function Polyform(x::Symbol, fns)
    p = universal_polynomial_ring(QQ)
    sx = gen(p, x)
    Polyform(sx, Dict([sx => fns[x]]))
end

function Base.show(io::IO, p::Polyform)
    if isone(p.denom)
        show(io, p.p)
    else
        print(io, "(")
        if p.p isa Number || operation(p.p) == +
            print(io,"(")
        end
        show(io, p.p)
        if p.p isa Number || operation(p.p) == +
            print(io,")")
        end
        print(io, " / ")
        if p.denom isa Number || operation(p.denom) == +
            print(io,"(")
        end
        show(io, p.denom)
        if p.denom isa Number || operation(p.denom) == +
            print(io,")")
        end
        print(io, ")")
    end
end

macro variables(xs...)
    Polyform.(xs)
end

# Terminterface for universal poly
TermInterface.isexpr(x::UniversalPolyRingElem) = iscall(x)
TermInterface.iscall(x::UniversalPolyRingElem) = !is_gen(x)
function TermInterface.operation(x::UniversalPolyRingElem)
    if length(x) == 1 #e.g. 2xy^2
        if length(vars(x)) == 1 && isone(coeff(x, 1)) #e.g. y^2 or sin(y)^2
            v, e = only(powers(x))
            if e == 1 #e.g. y or sin(y)
                return (*)
            else
                return (^)
            end
        else
            return (*)
        end
    else # e.g. x+y
        return (+)
    end
end
isconstant(p) = length(p) == 1 && isone(monomial(p, 1))
powers(m) = zip(vars(m), filter(x -> !iszero(x), exponent_vector(m, 1)))
function TermInterface.arguments(x::UniversalPolyRingElem)
    if length(x) == 1
        isconstant(x) && return [(coeff(x, 1))]
        c = coeff(x, 1)
        m = monomial(x, 1)

        if !isone(c)
            [c, (v^pow for (v, pow) in powers(m))...]
        else
            if length(vars(m)) == 1
                v, e = only(powers(m))
                if e == 1
                    return [v]
                else
                    [v, e]
                end
            else
                [v^pow for (v, pow) in powers(m)]
            end
        end
    elseif length(x) == 0
        [0]
    else
        ts = [Oscar.term(x, i) for i in 1:length(x)]
        return [isconstant(t) ?
                (coeff(t, 1)) : t for t in ts]
    end
end

# Terminterface for Polyform
SymbolicUtils.isexpr(x::Polyform) = iscall(x)
SymbolicUtils.iscall(x::Polyform) = !(isone(x.denom) && (!(x.p isa RingElem) || is_gen(x.p) && !haskey(x.fns, x.p)))
function TermInterface.operation(x::Polyform)
    !isone(x.denom) && return (/)
    is_gen(x.p) && haskey(x.fns, x.p) ? x.fns[x.p].op : TermInterface.operation(x.p)
end
tonumber(x) = try
    Int64(x)
catch
    Rational(x)
end
tonumber(x::Polyform) = x

function TermInterface.arguments(x::Polyform)
    if !is_one(x.denom)
        return cleanup.([Polyform(x.p, one(x.p), x.fns), Polyform(x.denom, one(x.p), x.fns)]; recurse=false)
    end

    if is_gen(x.p) && haskey(x.fns, x.p)
        return x.fns[x.p].args
    end

    return [p isa UniversalPolyRingElem ? cleanup(Polyform(p, one(p), x.fns); recurse=false) : tonumber(p) for p in TermInterface.arguments(x.p)]
end

# basic operations
function Oscar.vars(p::Polyform)
    r = []
    if p.p isa RingElem
        r = vcat(r, vars(p.p))
    end
    if p.denom isa RingElem
        r = vcat(r, vars(p.denom))
    end
    Set(r) #unique(r)
end

function cleanup(a; recurse=true)
    vs = repr.(vars(a))
    newfns = Dict([s => recurse ? cleanup(t) : t for (s, t) in a.fns if repr(s) in vs])
    Polyform(a.p, a.denom, newfns)
end

function updatediv(nom, denom, fns)
    q, r = divrem(nom, denom)
    iszero(r) && return cleanup(Polyform(q, one(q), fns); recurse=false)
    if iszero(q)
        d = gcd(r, denom)
        return cleanup(Polyform(r/d, denom/d, fns))
    end
    cleanup(Polyform(q*denom + r, denom, fns); recurse=false)
end

Base.promote_rule(::Type{T}, ::Type{Polyform}) where T <: Number = Polyform
Base.one(a::Polyform) = 1
Base.zero(a::Polyform) = 0
Base.:(*)(a::Polyform, b::Polyform) = updatediv(a.p*b.p, a.denom*b.denom, merge(a.fns, b.fns))
Base.:(+)(a::Polyform, b::Polyform) = updatediv(a.p*b.denom + b.p*a.denom, a.denom*b.denom, merge(a.fns, b.fns))
Base.:(/)(a::Polyform, b::Polyform) = updatediv(a.p*b.denom, a.denom*b.p, merge(a.fns, b.fns))
Base.:(-)(a::Polyform, b::Polyform) = a + (-b)
Base.:(-)(a::Polyform) = -1*a

function fold(x)
    if iscall(x)
        operation(x)([tonumber(fold(a)) for a in arguments(x)]...)
    else
        x
    end
end

function Base.iszero(a::Polyform)
    p = fold(a)
    p isa Polyform ? iszero(p.p) : iszero(p)
end
Base.:(==)(a::Polyform, b::Polyform) = iszero(a - b)

# For sorting IVs of derivatives
Base.isless(a::Polyform, b::Polyform) = isless(a.p, b.p)
SymbolicUtils.isnegative(a::Polyform) = false

# for substitution using Symbolicutils
Base.hash(x::Polyform) = hash(x.p, hash(x.denom))
SymbolicUtils.substitute(x, subs::Pair...) = substitute(x, Dict(subs))

# non polynomial functions
struct Fn
    op
    args
end

cleanup(a::Fn) = Fn(a.op, map(cleanup, a.args))

function makeop(op, args...)
    name = Symbol(op == identity ? "($(join(args, ",")))" : "$op($(join(args, ",")))")
    sx = gen(R, name)
    Polyform(sx, one(sx), Dict([sx => Fn(op, args)]))
end

SymbolicUtils.@number_methods(Polyform, makeop(f, a), makeop(f, a, b), skipbasics)

# functionals
struct Functional
    s
end

(fn::Functional)(x...) = makeop(fn, x...)
Base.show(io::IO, fn::Functional) = print(io, fn.s)

