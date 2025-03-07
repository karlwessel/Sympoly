### A Pluto.jl notebook ###
# v0.20.4

using Markdown
using InteractiveUtils

# ╔═╡ 589130c5-0ae3-4a43-8ea9-5342848dd695
using Pkg

# ╔═╡ 7aa1e756-1683-463c-8b9e-6ef65dad5f41
Pkg.activate(temp=true)

# ╔═╡ 93cfd37b-3c83-4361-9773-f24ef805b8fe
begin
	Pkg.add(url="https://github.com/karlwessel/Sympoly")
	Pkg.add(["LinearAlgebra", "Combinatorics", "SymbolicUtils"])
end

# ╔═╡ 1df249b1-eff3-432d-980e-3ab2e6700d42
using Sympoly

# ╔═╡ 812ff2be-1328-4095-8423-5eb82104c720
using Combinatorics

# ╔═╡ f37f80d7-dfea-47a2-858e-14983567056f
using LinearAlgebra

# ╔═╡ b32fe487-889f-43ff-bad9-87f9cbed65f5
using SymbolicUtils

# ╔═╡ a21120aa-346b-4f06-9fd0-2221564b1bd8
using SymbolicUtils.Rewriters

# ╔═╡ a66fef1d-11a7-4b48-9764-6e5a95e6352b
md"""
# Symbolic variables
"""

# ╔═╡ 5b87a70f-3226-4a02-a06d-7802bf462bcd
r = @variables x y z

# ╔═╡ 4d342204-3157-45ec-b88b-96fd198743dc
t, = @variables t

# ╔═╡ c96dba35-c3da-45a8-b982-9bf6ef7ce12b
k, pis, Rm, w, s = @variables k π Rm w s

# ╔═╡ 43a64f2e-43c9-4a96-910d-a6c518ce23af
x, y, z = r

# ╔═╡ 2be13b09-fd4b-460f-a856-fcc96a38c3dd
md"""
# Symbolic functions
"""

# ╔═╡ 8fbd807b-1f18-43f4-b74b-f543e7ea244a
u = [ f(x, y, z) for f in Functional.([:ux, :uy, :uz])]

# ╔═╡ 36610c34-e8db-43de-b6e2-c34b13fb5673
B = [f(z, t) for f in Functional.([:Bx, :By, :Bz])]

# ╔═╡ 32a47950-8a10-4f62-801b-aa72649a5618
md"""
# Derivatives
"""

# ╔═╡ a3108439-eb51-4d02-b8b2-50a6e0709558
Dt = Derivative(t)

# ╔═╡ b3c6a347-f386-4694-b91b-b75bf15e5c45
D = Derivative.(r)

# ╔═╡ ab3bc2a6-a4d2-410e-86a1-5734c9768017
curl(x) = [sum([levicivita([i,j,k])*D[j](x[k]) for j in 1:3, k in 1:3]) for i in 1:3]

# ╔═╡ d718fb69-4d78-4fe4-865a-9e972cd02ba8
divergence(x) = sum(D[i](x[i]) for i in 1:3)

# ╔═╡ 27283c23-df19-4131-bf96-4221388cf776
laplace(x) = sum(d(d(x)) for d in D)

# ╔═╡ 06b36272-de6a-4a50-80c3-8b251e393008
# directional derivative
dir(a, b) = sum([a[i] * D[i](b) for i in 1:3])

# ╔═╡ 6cf7ba1a-280d-4a32-af8b-5f8294d808ab
md"""
Derivatives are merged and comparable, this gives things like $\nabla\cdot(\nabla \times v) = 0$ for free
"""

# ╔═╡ 33cba5fc-bec8-4546-8b87-ea3263247fcb
0 == divergence(curl(u))

# ╔═╡ 26cf46a4-538f-498e-8d91-c3da69be5a09
md"""
# Integration
"""

# ╔═╡ 56c59160-64f3-4d1d-a2c8-6dd03e5c3f9c
md"""
The induction equation 

$$\partial_t B + \nabla \times \langle((B\cdot \nabla)u) \times u\rangle = \frac{1}{\text{Rm}} \nabla^2B$$

for the mean magnetic field $B$ and a given flow $u$, like it is used to solve kinematic Dynamo problems, serves as a good example how simple equations can be hard to solve manually, just because contain a lot of terms.
"""

# ╔═╡ 1a9dc7f6-9de2-41d9-a6d3-b76711cdff02
intx, inty = Integral.([x, y], 0, 1)

# ╔═╡ 6a901902-aba7-4b0c-86c0-83d93ca78cf7
xyaverage(v) = inty(intx(v))

# ╔═╡ b6d19cac-eb96-4093-992c-6317d15ced9e
eqmag = Dt.(B) + (curl(xyaverage.((dir.(Ref(B), u)) × u))) - 1/Rm * (laplace.(B))

# ╔═╡ b4035a5f-789f-4953-b0bb-57d218ee9e1e
md"""
Long equation with a lot of terms are better printed using `inspect(p)`:
"""

# ╔═╡ fb8f5084-178e-4a35-a321-3da8bf77ab07
inspect(eqmag[1])

# ╔═╡ 24ed8858-e348-4691-a03a-73dab1a59bc4
md"""
# Substitution
"""

# ╔═╡ b7b23942-8a18-44b6-bfa2-4397b841027b
md"""
The G.O. Roberts flow

$$u_R=\begin{pmatrix}\sin(2\pi x)\cos(2\pi y)\\\cos(2\pi x)\sin(2\pi y)\\w\sin(2\pi x)\sin(2\pi y)\end{pmatrix}$$

is a typical example for a flow that results in growing mean magnetic field (a dynamo)

$$B_R \propto \begin{pmatrix}cos(kx)\\sin(ky\\0\end{pmatrix}.$$
"""

# ╔═╡ 45f9e92d-e9f6-4c67-bef2-253843545e8f
uR = [sin(2pis*x)*cos(2pis*y), -cos(2pis*x)*sin(2pis*y), w*sin(2pis*x)*sin(2pis*y)]

# ╔═╡ 6c6a6c27-3053-4230-8b9e-532721d3b7f1
BR = exp(s*t)*[cos(k*z), sin(k*z), 0]

# ╔═╡ 298ac80a-83b5-4e65-a704-d619b01c2466
md"""
After substituting the unknown function $u$ and $B$ with known solutions, the derivatives are executed immediately and the equations become much shorter.
"""

# ╔═╡ 0a5a5f91-f0a8-48a0-9df6-da88cc989b93
eq0 = substitute.(eqmag, Ref(Dict([B .=> BR; u .=> uR])))

# ╔═╡ fc9814ce-9b87-4a45-bc70-01f7a62fc83f
md"""
# Rule-based term rewriting
"""

# ╔═╡ 5b01f435-816e-4941-816d-e8c163ddd1f7
md"""
We can help solving terms with $\int sin^2(x)$ by using term based rewriting to substitute $sin^2$ and $cos^2$ with their multiple angle identities.
"""

# ╔═╡ 08a1ff42-3090-4802-8cf4-27fb10cf80b6
rsin = @rule sin(~x)^2 => (1-cos(2*(~x))) / 2

# ╔═╡ 5f7ebe49-1a39-441c-aed6-c09ec20bb4ce
rcos = @rule cos(~x)^2 => (1+cos(2*(~x))) / 2

# ╔═╡ deb7c562-5600-406d-aaf1-d603553580fc
trigsimplify(x) = simplify(x, Postwalk(Chain([rcos, rsin])))

# ╔═╡ 12bce65b-695e-414c-b70b-ece972a85016
md"""
Irrational constants like $\pi$ aren't handled very well yet, therefore $sin(4\pi)$ has to be solved using term rewriting.
"""

# ╔═╡ b8673b11-dae9-4851-8168-84fb3f323999
dynamocond = substitute.(trigsimplify.(eq0), sin(4*pis) => 0)

# ╔═╡ 8268ff8e-1c32-4b1a-843d-2e09fca3e84e
inspect(dynamocond[1])

# ╔═╡ 2db2262c-4d25-4f40-960a-64eaa0364ebf
md"""
This gives an equation for the growth rate $s$ of the mean magnetic field.
"""

# ╔═╡ ff705db7-69c5-4c03-bbde-04fe86968b32
ssol = pis*w*k - k^2/Rm 

# ╔═╡ cb43211a-f302-4250-96fb-e5c33b257ef4
substitute.(dynamocond, s => ssol)

# ╔═╡ 73addd77-0e36-4e94-9823-5e6a93c1cc01
md"""
When the growth rate $s=\pi w k - k^2/\text{Rm} =0$ is zero, the magnetic field just starts to grow. This gives a value for the critical magnetic Reynolds number $Rm_c=k/\pi w$ at which value Dynamo action starts.
"""

# ╔═╡ b0256046-3c5e-40a6-8e2f-dd2f64ad3cc7
Rmc = k/(pis*w)

# ╔═╡ 09532c7e-bc66-4ee3-849f-32e08768d9bb
substitute(ssol, Rm => Rmc)

# ╔═╡ Cell order:
# ╠═589130c5-0ae3-4a43-8ea9-5342848dd695
# ╠═7aa1e756-1683-463c-8b9e-6ef65dad5f41
# ╠═93cfd37b-3c83-4361-9773-f24ef805b8fe
# ╠═1df249b1-eff3-432d-980e-3ab2e6700d42
# ╠═812ff2be-1328-4095-8423-5eb82104c720
# ╠═f37f80d7-dfea-47a2-858e-14983567056f
# ╟─a66fef1d-11a7-4b48-9764-6e5a95e6352b
# ╠═5b87a70f-3226-4a02-a06d-7802bf462bcd
# ╠═4d342204-3157-45ec-b88b-96fd198743dc
# ╠═c96dba35-c3da-45a8-b982-9bf6ef7ce12b
# ╠═43a64f2e-43c9-4a96-910d-a6c518ce23af
# ╟─2be13b09-fd4b-460f-a856-fcc96a38c3dd
# ╠═8fbd807b-1f18-43f4-b74b-f543e7ea244a
# ╠═36610c34-e8db-43de-b6e2-c34b13fb5673
# ╟─32a47950-8a10-4f62-801b-aa72649a5618
# ╠═a3108439-eb51-4d02-b8b2-50a6e0709558
# ╠═b3c6a347-f386-4694-b91b-b75bf15e5c45
# ╠═ab3bc2a6-a4d2-410e-86a1-5734c9768017
# ╠═d718fb69-4d78-4fe4-865a-9e972cd02ba8
# ╠═27283c23-df19-4131-bf96-4221388cf776
# ╠═06b36272-de6a-4a50-80c3-8b251e393008
# ╟─6cf7ba1a-280d-4a32-af8b-5f8294d808ab
# ╠═33cba5fc-bec8-4546-8b87-ea3263247fcb
# ╟─26cf46a4-538f-498e-8d91-c3da69be5a09
# ╟─56c59160-64f3-4d1d-a2c8-6dd03e5c3f9c
# ╠═1a9dc7f6-9de2-41d9-a6d3-b76711cdff02
# ╠═6a901902-aba7-4b0c-86c0-83d93ca78cf7
# ╠═b6d19cac-eb96-4093-992c-6317d15ced9e
# ╟─b4035a5f-789f-4953-b0bb-57d218ee9e1e
# ╠═fb8f5084-178e-4a35-a321-3da8bf77ab07
# ╟─24ed8858-e348-4691-a03a-73dab1a59bc4
# ╟─b7b23942-8a18-44b6-bfa2-4397b841027b
# ╠═45f9e92d-e9f6-4c67-bef2-253843545e8f
# ╠═6c6a6c27-3053-4230-8b9e-532721d3b7f1
# ╟─298ac80a-83b5-4e65-a704-d619b01c2466
# ╠═0a5a5f91-f0a8-48a0-9df6-da88cc989b93
# ╟─fc9814ce-9b87-4a45-bc70-01f7a62fc83f
# ╠═b32fe487-889f-43ff-bad9-87f9cbed65f5
# ╠═a21120aa-346b-4f06-9fd0-2221564b1bd8
# ╟─5b01f435-816e-4941-816d-e8c163ddd1f7
# ╠═08a1ff42-3090-4802-8cf4-27fb10cf80b6
# ╠═5f7ebe49-1a39-441c-aed6-c09ec20bb4ce
# ╠═deb7c562-5600-406d-aaf1-d603553580fc
# ╟─12bce65b-695e-414c-b70b-ece972a85016
# ╠═b8673b11-dae9-4851-8168-84fb3f323999
# ╠═8268ff8e-1c32-4b1a-843d-2e09fca3e84e
# ╟─2db2262c-4d25-4f40-960a-64eaa0364ebf
# ╠═ff705db7-69c5-4c03-bbde-04fe86968b32
# ╠═cb43211a-f302-4250-96fb-e5c33b257ef4
# ╟─73addd77-0e36-4e94-9823-5e6a93c1cc01
# ╠═b0256046-3c5e-40a6-8e2f-dd2f64ad3cc7
# ╠═09532c7e-bc66-4ee3-849f-32e08768d9bb
