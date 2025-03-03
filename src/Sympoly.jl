module Sympoly
using Oscar
using SymbolicUtils
import TermInterface

export @variables

R = universal_polynomial_ring(QQ)

struct Polyform <: Base.Real
    p
    denom
    fns
end

Polyform(x) = Polyform(x, one(x), Dict([]))

function Polyform(x::Symbol)
    sx = gen(R, x)
    Polyform(sx)
end

function Base.show(io::IO, p::Polyform)
	!isone(p.denom) && print(io, "(")
	SymbolicUtils.show_term(io, p.p)

	if !isone(p.denom)
		print(io, " / ")
		SymbolicUtils.show_term(io, p.denom)
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
SymbolicUtils.iscall(x::Polyform) = !isone(x.denom) || !is_gen(x.p) || haskey(x.fns, x.p)
function TermInterface.operation(x::Polyform)
	!isone(x.denom) && return (/)
	is_gen(x.p) && haskey(x.fns, x.p) ? x.fns[x.p].op : TermInterface.operation(x.p)
end
tonumber(x) = try
	Int64(x)
catch
	Rational(x)
end
function TermInterface.arguments(x::Polyform)
	if !is_one(x.denom)
		return [Polyform(x.p, one(x.p), x.fns), Polyform(x.denom, one(x.p), x.fns)]
	end

	if is_gen(x.p) && haskey(x.fns, x.p)
		return x.fns[x.p].args
	end

	return [p isa UniversalPolyRingElem ? Polyform(p, one(p), x.fns) : tonumber(p) for p in TermInterface.arguments(x.p)]
end

# basic operations
function cleanup(a; recurse=true)
	newfns = Dict([s => recurse ? cleanup(t) : t for (s, t) in a.fns if s in vars(a.p) || s in vars(a.denom)])
	Polyform(a.p, a.denom, newfns)
end

function updatediv(nom, denom, fns)
	q, r = divrem(nom, denom)
	iszero(r) && return cleanup(Polyform(q, one(q), fns))
	cleanup(Polyform(q*denom + r, denom, fns))
end

Base.promote_rule(::Type{T}, ::Type{Polyform}) where T <: Number = Polyform
Base.promote_rule(::Type{UnivPoly}, ::Type{Polyform}) = Polyform
Base.one(a::Polyform) = one(a.p)
Base.zero(a::Polyform) = zero(a.p)
Base.:(*)(a::Polyform, b::Polyform) = updatediv(a.p*b.p, a.denom*b.denom, merge(a.fns, b.fns))
Base.:(+)(a::Polyform, b::Polyform) = updatediv(a.p*b.denom + b.p*a.denom, a.denom*b.denom, merge(a.fns, b.fns))
Base.:(/)(a::Polyform, b::Polyform) = updatediv(a.p*b.denom, a.denom*b.p, merge(a.fns, b.fns))
Base.:(-)(a::Polyform, b::Polyform) = a + (-one(a)*b)


# non polynomial functions

end
