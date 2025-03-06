# Sympoly
This is a test on how far one gets with a [Polyform](https://docs.sciml.ai/SymbolicUtils/stable/manual/representation/#Polynomial-representation) based CAS System. It uses [Oscar](https://github.com/oscar-system/Oscar.jl) instead of [DynamicPolynomials](https://github.com/JuliaAlgebra/DynamicPolynomials.jl) to represent polynomials. More or less just for testing purposes. The former has the advantage of providing polynomial factorization, the latter has integration...

It also is somewhat a tribute to the Julia ecosystem, that allows to implement a basic version like this with relatively few lines of code:
 - Oscar + DiffRules for derivatives
 - TermInterface + SymbolicUtils for substitution and rule based term rewriting
 - like in Symbolics, julias Complex type could probably be used to support complex numbers.
Guiding principles of the first iteration:
 1. Be good for solving equation with a lot of terms, where each term is simple and may be easily solved by a human, but doing that for a lot of terms would be tedious and error prone. A typical use case for this can be equations involving vector differentials, like the Navier-Stokes equation, or doing perturbation expansions, or both together.
 2. The form of the equation given by the user is not sacred, the CAS can rewrite it freely as it sees fit. In the, the user can still rewrite the result into a more human suitable form. The CAS can help with that step, but don't has to. This allows the CAS to be good at the first principle. The intermediate results are long and convoluted and wouldn't be human parsable anyway. The end result will be short to be of any use, so it doesn't matter to much if it has a nice human readable form.
# Conclusion from first iteration
A third guiding principle proved necessary during development:
If in doubt, evaluate eagerly. There is not much reason behind this except that I had to decide on a guiding direction in this regard, just to not have to redecide on this for each coding decision. Her are some concrete decisions:
 - always immediately execute derivatives as much as possible, except when doing the chain rule would result in a not yet expandable derivative with respect to a term more complicated than a single variable.
 - if an evaluation results in julia number, don't wrap it into a Polyform, but return it as is. The next call using that result can still wrap it if necessary
 - immediately reevaluate an expression after substitutions

If this principle results in to much performance problems it can still be thrown away. But until then it makes development much easier.
[![CI](https://github.com/karlwessel/Sympoly/actions/workflows/CI.yml/badge.svg)](https://github.com/karlwessel/Sympoly/actions/workflows/CI.yml)
