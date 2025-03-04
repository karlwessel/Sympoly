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

function Oscar.vars(p::Polyform)
	r = []
	if p.p isa RingElem
		r = vcat(r, vars(p.p))
	end
	if p.denom isa RingElem
		r = vcat(r, vars(p.denom))
	end
	unique(r)
end

function occursin(f::Fn, x)
	for a in f.args
		occursin(a, x) && return true
	end
	return f.op isa Integral && f.op.iv == x
end

isgen(p::Polyform) = !iscall(p)
function occursin(p::Polyform, x)
	if isgen(x)
		x.p in vars(p) && return true
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

function integrate(p, x, from, to)
	hasx(p) = occursin(p, x)
	Integ = Integral(x, from, to)
	!hasx(p) && return p*(to - from)
	isgen(p) && isgen(x) && p.p == x.p && return 1//2*(to^2 - from^2)

	intmap = Dict([cos => sin, 
		sin => x -> -cos(x)])

	op = operation(p)
	if op == *
		argswithx = filter(hasx, arguments(p))
		argswithoutx = setdiff(arguments(p), argswithx)
		if length(argswithx) > 1
			return *(makeop(Integ, *(argswithx...)), argswithoutx...)
		end
		return *(Integ(only(argswithx)), argswithoutx...)
	elseif op == +
		return sum(map(Integ, arguments(p)))
	elseif haskey(intmap, op)
		y = only(arguments(p))
		intop = intmap[op]
		dy = derive(y, x)
		if !hasx(dy) && isconstant(dy.p)
			return 1//rationalize(tonumber(coeff(dy.p,1))) * rationalize(intop(substitute(y, x => to)) - intop(substitute(y, x => from)))
		end
	end

	return makeop(Integral(x, from, to), p)
end
