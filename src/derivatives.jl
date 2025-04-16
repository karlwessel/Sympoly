struct Derivative
    ivs
    # ivs are sorted so that derivatives of same ivs are considered equal
    Derivative(x::Array) = new(sort(x))
end
(D::Derivative)(x::Number) = 0

derive(a::Number, iv) = 0

SymbolicUtils.substitute(D::Derivative, dict; fold=true) = Derivative([substitute(iv, dict; fold) for iv in D.ivs])

Nemo.derivative(a::Number, x) = 0 # takes care of derive(Polyform(3), x)
function localderive(a::Polyform, iv)
    Polyform(derivative(a.p, iv), a.denom, a.fns)
end

function derive(a::Polyform, iv)
    a == iv && return 1
    denom = cleanup(Polyform(a.denom, one(a.p), a.fns); recurse=false)
    if !occursin(denom, iv)
        a = docleanup(a)
        p = sum([localderive(a, gen(R, k))*derive(t, iv) for (k, t) in a.fns]; init = occursin(a.p, iv.p) ? localderive(a, iv.p) : zero(a))
    else
        nom = cleanup(Polyform(a.p, one(a.p), a.fns); recurse=false)
        p = (derive(nom, iv)*denom - derive(denom, iv)*nom) / denom^2
    end
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

function derive(a::FnCall, iv)
    if a.op == identity
        derive(only(a.args), iv)
    elseif a.op isa Integral
        if occursin(a.op.from, iv) || occursin(a.op.to, iv)
            makeop(Derivative(iv), makeop(a.op, a.args...))
        elseif a.op.iv == iv
            0
        else
            return a.op(derive(only(a.args), iv))
        end
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
        dvs = [derive(arg, iv)*makeop(Derivative(arg), a.op(a.args...)) for arg in a.args if occursin(a, iv)]
        if isempty(dvs)
            return 0
        else
            return makeop(Derivative(iv), makeop(a.op, a.args...))#sum(dvs)
        end
        sum([derive(arg, iv)*makeop(Derivative(arg), a.op(a.args...)) for arg in a.args])
    else
        diff = diffrule(a.op, a.args...)
        if isnothing(diff)
            dvs = [derive(arg, iv)*makeop(Derivative(arg), a.op(a.args...)) for arg in a.args if occursin(a, iv)]
            if isempty(dvs)
                return 0
            else
                return makeop(Derivative(iv), makeop(a.op, a.args...))#sum(dvs)
            end
        else
            derive(only(a.args), iv) * diff
        end
    end
end

isderived(x::Polyform) = all(isderived.(values(docleanup(x).fns)))
isderived(x::FnCall) = !(x.op isa Derivative) && all(isderived.(x.args))
isderived(x) = true

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
