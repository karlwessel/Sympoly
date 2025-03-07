# Sympoly
This is a test on how far one gets with a [Polyform](https://docs.sciml.ai/SymbolicUtils/stable/manual/representation/#Polynomial-representation) based CAS System. It uses [Oscar](https://github.com/oscar-system/Oscar.jl) instead of [DynamicPolynomials](https://github.com/JuliaAlgebra/DynamicPolynomials.jl) to represent polynomials. More or less just for testing purposes. The former has the advantage of providing polynomial factorization, the latter has integration...

It also is somewhat a tribute to the Julia ecosystem, that allows to implement a basic version like this with relatively few lines of code:
 - Oscar + [DiffRules](https://github.com/JuliaDiff/DiffRules.jl) for derivatives
 - [TermInterface](https://github.com/JuliaSymbolics/TermInterface.jl) + [SymbolicUtils](https://github.com/JuliaSymbolics/SymbolicUtils.jl) for substitution and rule based term rewriting
 - like in [Symbolics](https://github.com/JuliaSymbolics/Symbolics.jl), julias [Complex type](https://docs.julialang.org/en/v1/manual/complex-and-rational-numbers/#Complex-Numbers) could probably be used to support complex numbers.

# First steps
## Installation
From the REPL:
```julia repl
julia> using Pkg
julia> Pkg.add(url="https://github.com/karlwessel/Sympoly")
```
## Define symbolic variables

```julia
t, = @variables t
k, pis, Rm, w, s = @variables k π Rm w s
r = @variables x y z
x, y, z = r
```

## Define Symbolic functions
```julia
u = [f(x, y, z) for f in Functional.([:ux, :uy, :uz])]
B = [f(z, t) for f in Functional.([:Bx, :By, :Bz])]
```

## Derivatives
```julia
Dt = Derivative(t)
D = Derivative.(r)

using Combinatorics
curl(x) = [sum([levicivita([i,j,k])*D[j](x[k]) for j in 1:3, k in 1:3]) for i in 1:3]
divergence(x) = sum(D[i](x[i]) for i in 1:3)
laplace(x) = sum(d(d(x)) for d in D)
# directional derivative
dir(a, b) = sum([a[i] * D[i](b) for i in 1:3])
```
Derivatives are merged and comparable, this gives things like $\nabla\cdot(\nabla \times v) = 0$ for free:

```julia
iszero(divergence(curl(u)))
```
## Integral
Lets start to do some real calculation here. The induction equation 

$$\partial_t B + \nabla \times \langle((B\cdot \nabla)u) \times u\rangle = \frac{1}{\text{Rm}} \nabla^2B$$

for the mean magnetic field $B$ and a given flow $u$, like it is used to solve kinematic Dynamo problems, serves as a good example how simple equations can be hard to solve manually, just because they contain a lot of terms.

```julia
using LinearAlgebra

intx, inty = Integral.([x, y], 0, 1)
xyaverage(v) = inty(intx(v))
eqmag = Dt.(B) + (curl(xyaverage.((dir.(Ref(B), u)) × u))) - 1/Rm * (laplace.(B))
```

Long equation with a lot of terms are better printed using `inspect(p)`:

```julia
inspect(eqmag[1])
```

## Substitution
The G.O. Roberts flow

$$u_R=\begin{pmatrix}\sin(2\pi x)\cos(2\pi y)\\ 
\cos(2\pi x)\sin(2\pi y)\\ 
w \sin(2\pi x)\sin(2\pi y)\end{pmatrix}$$

is a typical example for a flow that results in growing mean magnetic field (a dynamo) with a growth rate $s$

$$B_R \propto \exp(st)\begin{pmatrix}\cos(kx)\\ 
\sin(ky)\\ 
0 \end{pmatrix}.$$

```julia
uR = [sin(2pis*x)*cos(2pis*y), 
	-cos(2pis*x)*sin(2pis*y), 
	w*sin(2pis*x)*sin(2pis*y)]
BR = exp(s*t)*[cos(k*z), sin(k*z), 0]

eq0 = substitute.(eqmag, Ref(Dict([B .=> BR; u .=> uR])))
```
After substituting the unknown function $u$ and $B$ with known solutions, the derivatives are executed immediately and the equations become much shorter.

# Rule-based term rewriting
We can help solving terms with $\int sin^2(x)$ by using term based rewriting to substitute $sin^2$ and $cos^2$ with their multiple angle identities.

```julia
using SymbolicUtils
using SymbolicUtils.Rewriters

rsin = @rule sin(~x)^2 => (1-cos(2*(~x))) / 2
rcos = @rule cos(~x)^2 => (1+cos(2*(~x))) / 2
trigsimplify(x) = simplify(x, Postwalk(Chain([rcos, rsin])))

dynamocond = substitute.(trigsimplify.(eq0), sin(4*pis) => 0)
```

Irrational constants like $\pi$ aren't handled very well yet, therefore $sin(4\pi)$ has to be solved using term rewriting.

If we want we can now complete the dynamo calculation. The equation in `dynamocond` above gives an equation for the growth rate $s$ of the mean magnetic field.

```julia
ssol = pis*w*k - k^2/Rm

iszero.(substitute.(dynamocond, s => ssol))
```

When the growth rate $s=\pi w k - k^2/\text{Rm} =0$ is zero, the magnetic field just starts to grow. This gives a value for the critical magnetic Reynolds number $Rm_c=k/\pi w$ at which Dynamo action starts.

```julia
Rmc = k/(pis*w)

iszero(substitute(ssol, Rm => Rmc))
```

# Guiding principles of the first iteration
 1. Be good for solving equation with a lot of terms, where each term is simple and may be easily solved by a human, but doing that for a lot of terms would be tedious and error prone. A typical use case for this can be equations involving vector differentials, like the Navier-Stokes equation, or doing perturbation expansions, or both together.
 2. The form of the equation given by the user is not sacred, the CAS can rewrite it freely as it sees fit. In the, the user can still rewrite the result into a more human suitable form. The CAS can help with that step, but don't has to. This allows the CAS to be good at the first principle. The intermediate results are long and convoluted and wouldn't be human parsable anyway. The end result will be short to be of any use, so it doesn't matter to much if it has a nice human readable form.
# Conclusion from first iteration
A third guiding principle proved necessary during development:
If in doubt, evaluate eagerly. There is not much reason behind this except that I had to decide on a guiding direction in this regard, just to not have to redecide on this for each coding decision. Her are some concrete decisions:
 - always immediately execute derivatives as much as possible, except when doing the chain rule would result in a not yet expandable derivative with respect to a term more complicated than a single variable.
 - if an evaluation results in julia number, don't wrap it into a Polyform, but return it as is. The next call using that result can still wrap it if necessary
 - immediately reevaluate an expression after substitutions
 - fail early on floats but take care of correct handling of irrational constants
 - add an interface to add simple integration rules, similar to diff rules, so that users can easily define the simple integrals occuring in their equations

If this principle results in to much performance problems it can still be thrown away. But until then it makes development much easier.
[![CI](https://github.com/karlwessel/Sympoly/actions/workflows/CI.yml/badge.svg)](https://github.com/karlwessel/Sympoly/actions/workflows/CI.yml)
