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
	
function occursin(p::Polyform, x)
	p == x && return true
	!iscall(p) && return false
	for a in arguments(p)
		occursin(a, x) && return true
	end
	return false
end

occursin(p::Number, x) = p == x

function integrate(p, x, from, to)
	hasx(p) = occursin(p, x)
	Integ = Integral(x, from, to)
	!hasx(p) && return p*(to - from)
	p == x && return 1//2*(to^2 - from^2)

	intmap = Dict([cos => sin, 
		sin => x -> -cos(x)])

	op = operation(p)
	if op == *
		argswithx = filter(hasx, arguments(p))
		if length(argswithx) > 1
			return makeop(Integ, p)
		end
		return *(Integ(only(argswithx)), setdiff(arguments(p), argswithx)...)
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
