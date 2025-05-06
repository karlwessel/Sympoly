R = universal_polynomial_ring(QQ)

struct Polyform <: Integer
    p::Generic.UnivPoly{QQFieldElem}
    fns
    isclean
end
symbolmap = Dict{RingElem, Symbol}()

hasfn(p, s::Symbol) = haskey(p.fns, s)
hasfn(p, s) = hasfn(p, symbolmap[s])
getfn(p, var::Symbol) = p.fns[var]
getfn(p, var) = getfn(p, symbolmap[var])

const Polylike = Union{Polyform, Rational{Polyform}}

Polyform(x) = Polyform(R(x), Dict([]), true)
Polyform(x::AbstractFloat) = Polyform(tonumber(x))
Polyform(x::Irrational{T}) where T = makeconstant(T)
Polyform(p::RingElem, fns) = Polyform(p, fns, true)
Polyform(p, fns) = Polyform(R(p), fns)
Polyform(x::Polylike) = x

function Polyform(x::Symbol)
    sx = gen(R, x)
    symbolmap[sx] = x
    Polyform(sx, Dict([]))
end

function Polyform(x::Symbol, fns)
    sx = gen(R, x)
    symbolmap[sx] = x
    Polyform(sx, fns)
end


Base.show(io::IO, p::Polyform) = show(io, p.p)
function Base.show(io::IO, p::Rational{Polyform})
    n, d = numerator(p), denominator(p)
    if isone(d)
        show(io, n)
    else
        print(io, "(")
        if n.p isa Number || operation(n.p) == +
            print(io,"(")
        end
        show(io, n.p)
        if n.p isa Number || operation(n.p) == +
            print(io,")")
        end
        print(io, " / ")
        if d.p isa Number || operation(d.p) == +
            print(io,"(")
        end
        show(io, d.p)
        if d.p isa Number || operation(d.p) == +
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
TermInterface.iscall(x::UniversalPolyRingElem) = !(is_gen(x) || isconst(x))
function TermInterface.operation(x::UniversalPolyRingElem)
    if length(x) == 1 #e.g. 2xy^2
        if length(vars(x)) == 1 && isone(coeff(x, 1)) #e.g. y^2 or sin(y)^2
            return (^)
        else
            return (*)
        end
    else # e.g. x+y
        return (+)
    end
end
isconst(p::RingElem) = length(p) == 0 || length(p) == 1 && isone(monomial(p, 1))
isconst(p::Polyform) = isconst(p.p)
isconst(x) = true

coefficient(p::RingElem) = length(p) == 0 ? 0 : tonumber(coeff(p, 1))
coefficient(p::Polyform) = coefficient(p.p)
coefficient(x) = x

powers(m) = zip(vars(m), filter(x -> !iszero(x), exponent_vector(m, 1)))
function TermInterface.arguments(x::UniversalPolyRingElem)
    if length(x) == 1
        c = coefficient(x)
        m = monomial(x, 1)

        if !isone(c)
            [c, m]
        else
            if length(vars(m)) == 1
                v, e = only(powers(m))
                return [v, e]
            else
                return [v^pow for (v, pow) in powers(m)]
            end
        end
    else
        ts = [Nemo.term(x, i) for i in 1:length(x)]
        return [isconst(t) ? coefficient(t) : t for t in ts]
    end
end

# Terminterface for Rational Polyform
TermInterface.iscall(x::Rational{Polyform}) = true
function TermInterface.operation(x::Rational{Polyform})
    return (//)
end
function TermInterface.arguments(x::Rational{Polyform})
    return [numerator(x), denominator(x)]
end

# Terminterface for Complex Polyform
TermInterface.isexpr(x::Complex{Polyform}) = iscall(x)
TermInterface.iscall(x::Complex{Polyform}) = true
function TermInterface.operation(x::Complex{Polyform})
    iszero(real(x)) ? (*) : (+)
end
function TermInterface.arguments(x::Complex{Polyform})
    if iszero(real(x))
        Any[im, imag(x)]
    else
        [real(x), im*imag(x)]
    end
end

# Terminterface for Polyform
TermInterface.isexpr(x::Polylike) = iscall(x)
TermInterface.iscall(x::Polyform) = iscall(x.p) || is_gen(x.p) && hasfn(x, x.p)
function TermInterface.operation(x::Polyform)
    return is_gen(x.p) && hasfn(x, x.p) ?
        getfn(x, x.p).op : TermInterface.operation(x.p)
end

trynumber(x) = try
    Int(x)
catch
    Rational(x)
end

tonumber(x::RingElem) = trynumber(Rational(x))
tonumber(x::Int64) = x
tonumber(x::Rational{Int64}) = trynumber(x)
tonumber(x::Rational{BigInt}) = trynumber(x)
tonumber(x::Polylike) = x
tonumber(x::AbstractIrrational) = x
tonumber(x::Float64) = Int64(round(x, digits=8))
tonumber(x::BigFloat) = Int64(round(x, digits=8))


function TermInterface.arguments(x::Polyform)
    if is_gen(x.p) && hasfn(x, x.p)
        return getfn(x, x.p).args
    end

    return [cleanup(Polyform(p, x.fns); recurse=false) for p in TermInterface.arguments(x.p)]
end

SymbolicUtils.maketerm(T::Type{<:Polylike}, head, args, metadata) = head(args...)

# basic operations
function Nemo.vars(p::Polyform)
    r = []
    if p.p isa RingElem
        r = vcat(r, vars(p.p))
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

invars(p::Polyform, x) = invars(p.p, x)
invarsv(p::Polyform, x::Vector) = invarsv(p.p, x)
invars(p::Number, x) = false
invarsv(p::Number, x) = zeros(Bool, length(x))

cleanup(a::Rational{Polyform}; recurse=true) = Rational(cleanup(numerator(a); recurse), cleanup(denominator(a); recurse))
function cleanup(a::Polyform; recurse=true)
    isempty(a.fns) && return a
    if recurse
        newfns = Dict([s => cleanup(t) for (s, t) in a.fns])
    else
        newfns = a.fns
    end
    Polyform(a.p, newfns, false)
end

function docleanup(a)
    #vs = vars(a)
    isempty(a.fns) && return a
    syms = collect(keys(a.fns))
    isin = syms[invarsv(a, gen.(Ref(R), syms))]
    newfns = Dict([s => a.fns[s] for s in isin])
    Polyform(a.p, newfns, true)
end

Base.promote_rule(::Type{Rational{T}}, ::Type{Polyform}) where T = Polyform
Base.promote_rule(::Type{T}, ::Type{Polyform}) where T <: Int = Polyform
Base.promote_rule(::Type{T}, ::Type{T2}) where {T <: AbstractIrrational, T2 <: Polylike} = T2
Base._irrational_to_rational(::Type{Polyform}, x::AbstractIrrational) = Rational(Polyform(x))
Base.one(a::Polyform) = Polyform(1)
Base.zero(a::Polyform) = Polyform(0)
Base.:(*)(a::Polyform, b::Polyform) = Polyform(a.p * b.p, merge(a.fns, b.fns))
Base.:(+)(a::Polyform, b::Polyform) = Polyform(a.p + b.p, merge(a.fns, b.fns))
Base.:(/)(a::Polyform, b::Polyform) = a // b
Base.:(//)(a::Polylike, b::AbstractIrrational) = a / Polyform(b)
Base.:(//)(a::AbstractIrrational, b::Polylike) = Polyform(a) / b
Base.:(-)(a::Polyform, b::Polyform) = a + (-b)
Base.:(-)(a::Polyform) = -1*a

# for Rational{Polyform} support
Base.uabs(x::Polyform) = x
function Base.gcd(x::Polyform, y::Polyform) 
    g = gcd(x.p, y.p)
    Polyform(gcd(content(x.p / g), content(y.p / g))*g, x.fns)
end
Base.div(x::Polyform, y::Polyform) = Polyform(div(x.p, y.p), x.fns)
Base.signbit(x::Polyform) = false
Base.checked_mul(x::Polyform, y::Polyform) = x * y
Base.checked_add(x::Polyform, y::Polyform) = x + y
Base.checked_sub(x::Polyform, y::Polyform) = x - y
Base.inv(x::Polyform) = 1/x

function Base.:(^)(a::Polyform, b::Polyform)
    n = makebase(b)
    if n isa Polyform
        makeop(^, a, b)
    else
        a ^ tonumber(n)
    end
end

Base.:(^)(a::Integer, b::Polyform) = Polyform(a)^b

function Base.iszero(p::Polyform)
    p isa Polyform ? iszero(p.p) : iszero(p)
end
# TODO: a == b should hash(a) == hash(b)
Base.:(==)(a::Polyform, b::Polyform) = a.p == b.p || iszero(a - b)

# For sorting IVs of derivatives
Base.isless(a::Polyform, b::Polyform) = isless(a.p, b.p)
SymbolicUtils.isnegative(a::Polyform) = false

# for substitution using Symbolicutils
Base.hash(x::Polyform, h::UInt) = hash(x.p, h)
Base.hash(x::Rational{Polyform}, h::UInt) = hash(numerator(x), hash(denominator(x), h))
SymbolicUtils.substitute(x, subs::Pair...) = substitute(x, Dict(subs))


makebase(a) = a
makebase(a::RingElem) = throw("makebase for RingElem?")

function makebase(a::Polyform)
    subs = Dict()
    for v in vars(a)
        s = symbolmap[v]
        if !haskey(a.fns, s)
            return a
        end
        
        fn = a.fns[s]
        
        cargs = map(makebase, fn.args)
        if any(x isa Polylike for x in cargs)
            return a
        end
        
        subs[v] = fn.op(cargs...)
    end
    n = substitute(a.p, subs)
    @assert isconst(n)
    
    # pi / 1 creates a float, we want to keep it a constant
    coefficient(n)
end

function makebase(a::Rational{Polyform})
    n = makebase(numerator(a))
    n === numerator(a) && return a
    d = makebase(denominator(a))
    d === denominator(a) && return a
    
    # pi / 1 creates a float, we want to keep it a constant
    isone(d) ? n : n / d
end

function tryfn(op, args::Polylike...)
    cargs = map(makebase, args)
    
    if any(x isa Polylike for x in cargs)
        return makeop(op, args...)
    end
    
    try
        Polyform(tonumber(op(cargs...)))
    catch e
        if e isa InexactError
            return makeop(op, args...)
        end
        rethrow(e)
    end
end

struct FnCall
    op
    args
end

cleanup(a::FnCall) = FnCall(a.op, map(cleanup, a.args))

function makeconstant(symb::Symbol)
    Polyform(symb, Dict([symb => FnCall(eval, [symb])]))
end

function makeop(op, args...)
    name = Symbol(op == identity ? "($(join(args, ",")))" : "$op($(join(args, ",")))")
    Polyform(name, Dict([name => FnCall(op, Polyform.(args))]))
end

SymbolicUtils.@number_methods(Polylike, tryfn(f, a), tryfn(f, a, b), skipbasics)

# functionals
struct Functional
    s
end

(fn::Functional)(x...) = makeop(fn, x...)
Base.show(io::IO, fn::Functional) = print(io, fn.s)

