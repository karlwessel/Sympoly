function inspect(p::Polyform, io = stdout)
    if length(p.p) == 0
        print(io, "0")
        return
    end
    facs = factor(data(p.p))
    !isone(unit(facs)) && print(io, unit(facs))
    for (f, e) in facs
        length(facs) > 1 && length(terms(f)) > 1 &&print(io, "[")
        termsperline = 7
        charactersperline = 30
        for (i, t) in enumerate(terms(f))
            termsperline -= 1
            r = repr(t)
            charactersperline -= length(r)
            if i > 1
                if termsperline < 0 || charactersperline < 0
                    print(io, "\n ")
                    termsperline = 7
                    charactersperline = max(0, charactersperline + 30)
                end
                if first(r) == '-'
                    r = r[2:end]
                    print(io, " - ")
                else
                    print(io, " + ")
                end
            end
            print(io, r)
        end
        length(facs) > 1 && length(terms(f)) > 1 && print(io, "]")
        !isone(e) && print(io, "^$e")
    end
    print(io, "\n")
end

function inspect(p::Rational{Polyform}, io = stdout)
    n, d = numerator(p), denominator(p)
    if isone(d)
        inspect(n, io)
    else
        q, r = divrem(n.p, d.p)
        if !iszero(q)
            inspect(Polyform(q, n.fns), io)
            if !iszero(r)
                print(io, " + ")
                inspect(Polyform(r, n.fns) / d, io)
            end
        elseif !iszero(r)
            print(io, "(")
            inspect(Polyform(r, n.fns), io)
            print(io,") / ( \n ")
            inspect(Polyform(d.p , n.fns), io)
            print(io, "\n)")
        end
    end
end