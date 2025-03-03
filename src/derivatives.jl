struct Derivative
	ivs
	# ivs are sorted so that derivatives of same ivs are considered equal
	Derivative(x::Array) = new(sort(x))
end
(D::Derivative)(x::Number) = 0

Oscar.derivative

Oscar.derivative(a::Number, x) = 0 # takes care of derive(Polyform(3), x)
nonrecurse_derive(a::Polyform, iv) = Polyform((derivative(a.p, iv)*a.denom - derivative(a.denom, iv)*a.p), a.denom^2, a.fns)
function derive(a::Polyform, iv)
	p = sum([nonrecurse_derive(a, k)*derive(t, iv) for (k, t) in a.fns]; init = nonrecurse_derive(a, iv.p))
	cleanup(p; recurse=false)
end

function diffrule(fn, x...)
	try
		r = DiffRules.diffrule(:Base, Symbol(fn), x...)
		eval(r)
	catch ex
		if ex isa KeyError
			return nothing
		end
		rethrow(ex)
	end	
end

function derive(a::Fn, iv)
	if a.op == identity
		derive(only(a.args), iv)
	elseif a.op isa Derivative
		r = derive(only(a.args), iv)
		# need to check iszero against polynomial instead of polyform,
		# otherwise folding of iszero would recurse into derivatives again
		if iszero(r.p) 
			r
		else
			ivs = vcat(iv, a.op.ivs...)
			makeop(Derivative(ivs), only(a.args))
		end
	elseif a.op isa Functional
		sum([derive(arg, iv)*makeop(Derivative(arg), a.op(a.args...)) for arg in a.args])
	else
		diff = diffrule(a.op, a.args...)
		if isnothing(diff)
			sum([derive(arg, iv)*makeop(Derivative(arg), a.op(a.args...)) for arg in a.args])
		else
			derive(only(a.args), iv) * diff
		end
	end
end

isderived(x::Polyform) = all(isderived.(values(x.fns)))
isderived(x::Fn) = !(x.op isa Derivative) && all(isderived.(x.args))

function (D::Derivative)(x::Polyform)
	r = x
	for c in permutations(D.ivs)
		r = x
		for iv in c
			r = derive(r, iv)
			# need to check iszero against polynomial instead of polyform,
			# otherwise folding of iszero would recurse into derivatives again
			if iszero(r.p)
				return r
			end
		end
		if isderived(r)
			return r
		end
	end
	r
end

Derivative(x) = Derivative([x])

Base.show(io::IO, D::Derivative) = print(io, "∂_[$(join(D.ivs))]")
