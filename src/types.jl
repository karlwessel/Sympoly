R = universal_polynomial_ring(QQ)

struct Polyform <: Base.Real
    p
    denom
    fns
    isclean
end
symbolmap = Dict{RingElem, Symbol}()

hasfn(p, s::Symbol) = haskey(p.fns, s)
hasfn(p, s) = hasfn(p, symbolmap[s])
getfn(p, var::Symbol) = p.fns[var]
getfn(p, var) = getfn(p, symbolmap[var])

Polyform(x) = Polyform(x, one(x), Dict([]), true)
Polyform(x::AbstractFloat) = Polyform(tonumber(x))
Polyform(x::AbstractIrrational) = makeop(identity, x)
Polyform(p, denom, fns) = Polyform(p, denom, fns, true)

function Polyform(x::Symbol)
    sx = gen(R, x)
    symbolmap[sx] = x
    Polyform(sx, one(sx), Dict([]))
end

function Polyform(x::Symbol, fns)
    sx = gen(R, x)
    symbolmap[sx] = x
    Polyform(sx, one(sx), fns)
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
        ts = [Nemo.term(x, i) for i in 1:length(x)]
        return [isconstant(t) ?
                (coeff(t, 1)) : t for t in ts]
    end
end

# Terminterface for Polyform
SymbolicUtils.isexpr(x::Polyform) = iscall(x)
SymbolicUtils.iscall(x::Polyform) = !(isone(x.denom) && (!(x.p isa RingElem) || is_gen(x.p) && !hasfn(x, x.p)))
function TermInterface.operation(x::Polyform)
    !isone(x.denom) && return (/)
    is_gen(x.p) && hasfn(x, x.p) ? getfn(x, x.p).op : TermInterface.operation(x.p)
end
tonumber(x) = try
    Int64(x)
catch
    Rational(x)
end
tonumber(x::Polyform) = x
tonumber(x::AbstractIrrational) = x

function TermInterface.arguments(x::Polyform)
    if !is_one(x.denom)
        return cleanup.([Polyform(x.p, one(x.p), x.fns), Polyform(x.denom, one(x.p), x.fns)]; recurse=false)
    end

    if is_gen(x.p) && hasfn(x, x.p)
        return getfn(x, x.p).args
    end

    return [p isa UniversalPolyRingElem ? cleanup(Polyform(p, one(p), x.fns); recurse=false) : tonumber(p) for p in TermInterface.arguments(x.p)]
end

SymbolicUtils.maketerm(T::Type{<:Polyform}, head, args, metadata) = head(args...)

# basic operations
function Nemo.vars(p::Polyform)
    r = []
    if p.p isa RingElem
        r = vcat(r, vars(p.p))
    end
    if p.denom isa RingElem
        r = vcat(r, vars(p.denom))
    end
    Set(r) #unique(r)
end


function invars(p, x)
    p = data(p)
    R = parent(p)
    n = nvars(R)
    idx = findfirst(exponent_vector(data(x), 1) .> 0)

    idx > n && return false

    z = Vector{Int64}(undef, n)
    for i in 1:length(p)
        exponent_vector!(z, p, i)
        !iszero(z[idx]) && return true
    end
    return false
end

function invarsv(p::RingElem, xs::Vector)
    p = data(p)
    R = parent(p)
    n = nvars(R)
    maxn = maximum(nvars.(parent.(data.(xs))))
    z = Vector{Int64}(undef, max(maxn, n))
    idxs = findfirst.([exponent_vector!(z, data(x), 1) .> 0 for x in xs])

    res = zeros(Bool, length(xs))


    for i in 1:length(p)
        exponent_vector!(z, p, i)
        for (j, idx) in enumerate(idxs)
            if !res[j] && !iszero(z[idx])
                res[j] = true
            end
        end
        if all(res[idxs .<= n])
            return res
        end
    end
    return res
end

invars(p::Polyform, x) = invars(p.p, x) || invars(p.denom, x)
invarsv(p::Polyform, x::Vector) = invarsv(p.p, x) .|| invarsv(p.denom, x)
invars(p::Number, x) = false
invarsv(p::Number, x) = zeros(Bool, length(x))

function cleanup(a; recurse=true)
    isempty(a.fns) && return a
    if recurse
        newfns = Dict([s => cleanup(t) for (s, t) in a.fns])
    else
        newfns = a.fns
    end
    Polyform(a.p, a.denom, newfns, false)
end

function docleanup(a)
    #vs = vars(a)
    isempty(a.fns) && return a
    syms = collect(keys(a.fns))
    isin = syms[invarsv(a, gen.(Ref(R), syms))]
    newfns = Dict([s => a.fns[s] for s in isin])
    Polyform(a.p, a.denom, newfns, true)
end

function updatediv(nom, denom, fns)
    q, r = divrem(nom, denom)
    iszero(r) && return cleanup(Polyform(q, one(q), fns); recurse=false)
    d = gcd(r, denom) * gcd(content(r), content(denom))
    ds = denom/d
    if iszero(q)
        return cleanup(Polyform(r/d, ds, fns); recurse=false)
    end
    cleanup(Polyform(q*ds + r/d, ds, fns); recurse=false)
end

function updatediv(nom, denom::Number, fns)
    d = gcd(tonumber(content(nom)), denom)
    Polyform(nom/d, tonumber(denom/d), fns)
end
function updatediv(nom::Number, denom, fns)
    d = gcd(nom, tonumber(content(denom)))
    Polyform(tonumber(nom/d), denom/d, fns)
end

Base.promote_rule(::Type{T}, ::Type{Polyform}) where T <: Number = Polyform
Base.promote_rule(::Type{T}, ::Type{Polyform}) where T <: AbstractIrrational = Polyform
Base.one(a::Polyform) = 1
Base.zero(a::Polyform) = 0
Base.:(*)(a::Polyform, b::Polyform) = isone(a.denom) && isone(b.denom) ? Polyform(a.p * b.p, one(a.p), merge(a.fns, b.fns)) : updatediv(a.p*b.p, a.denom*b.denom, merge(a.fns, b.fns))
Base.:(+)(a::Polyform, b::Polyform) = isone(a.denom) && isone(b.denom) ? Polyform(a.p + b.p, one(a.p), merge(a.fns, b.fns)) : updatediv(a.p*b.denom + b.p*a.denom, a.denom*b.denom, merge(a.fns, b.fns))
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
Base.:(==)(a::Polyform, b::Polyform) = a.p == b.p && a.denom == b.denom || iszero(a - b)

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
    Polyform(name, Dict([name => Fn(op, args)]))
end

SymbolicUtils.@number_methods(Polyform, makeop(f, a), makeop(f, a, b), skipbasics)

# functionals
struct Functional
    s
end

(fn::Functional)(x...) = makeop(fn, x...)
Base.show(io::IO, fn::Functional) = print(io, fn.s)

