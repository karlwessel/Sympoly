function inspect(p::Polyform, io = stdout)
    if isone(p.denom)
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
    else
        q, r = divrem(p.p, p.denom)
        if !iszero(q)
            inspect(Polyform(q, one(p.p), p.fns), io)
        end
        if !iszero(r)
            gc = gcd(r, p.denom)* gcd(content(r), content(p.denom))
            !iszero(q) && print(io," + ")
            print(io, "(")
            inspect(Polyform(r / gc, one(p.p), p.fns), io)
            print(io,") / ( \n ")
            inspect(Polyform(p.denom / gc, one(p.p), p.fns), io)
            print(io, "\n)")
        end
    end
end
