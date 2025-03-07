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

# ╔═╡ e6ee6b58-fa93-11ef-1964-f7002ccf43fc


# ╔═╡ b7bd4335-621e-4cb9-afab-de414b080a27


# ╔═╡ b2ea4e74-cec7-4b06-921d-028a97cacdc1


# ╔═╡ a66fef1d-11a7-4b48-9764-6e5a95e6352b
md"""
# Symbolic variables
"""

# ╔═╡ 5b87a70f-3226-4a02-a06d-7802bf462bcd
r = @variables x y z

# ╔═╡ c96dba35-c3da-45a8-b982-9bf6ef7ce12b
kv, kB, v0, pis, lambda, N, w = @variables kᵥ kB v₀ π λ N w

# ╔═╡ 43a64f2e-43c9-4a96-910d-a6c518ce23af
x, y, z = r

# ╔═╡ 2be13b09-fd4b-460f-a856-fcc96a38c3dd
md"""
# Symbolic functions
"""

# ╔═╡ 8fbd807b-1f18-43f4-b74b-f543e7ea244a
u = [ f(x, y, z) for f in Functional.([:ux, :uy, :uz])]

# ╔═╡ 36610c34-e8db-43de-b6e2-c34b13fb5673
B = [f(z) for f in Functional.([:Bx, :By, :Bz])]

# ╔═╡ 32a47950-8a10-4f62-801b-aa72649a5618
md"""
# Derivatives
"""

# ╔═╡ b3c6a347-f386-4694-b91b-b75bf15e5c45
D = Derivative.(r)

# ╔═╡ ab3bc2a6-a4d2-410e-86a1-5734c9768017
curl(x) = [sum([levicivita([i,j,k])*D[j](x[k]) for j in 1:3, k in 1:3]) for i in 1:3]

# ╔═╡ d718fb69-4d78-4fe4-865a-9e972cd02ba8
divergence(x) = sum(D[i](x[i]) for i in 1:3)

# ╔═╡ 27283c23-df19-4131-bf96-4221388cf776
lapl(x) = sum(d(d(x)) for d in D)

# ╔═╡ 06b36272-de6a-4a50-80c3-8b251e393008
# directional derivative
dir(a, b) = sum([a[i] * D[i](b) for i in 1:3])

# ╔═╡ 851e8f55-91df-47bd-b42a-63b3383e2664
md"""
Some syntactic sugar to write derivatives in terms of $\nabla$
"""

# ╔═╡ 57e7f8f7-0134-4dc2-bb9c-a0743f61e910
struct Nabla end

# ╔═╡ ce448d5d-9b34-4c6b-9fc7-b2efaea7959b
begin
	struct DirDeriv
		dir
	end
	(d::DirDeriv)(v) = dir(d.dir, v)
end

# ╔═╡ 5998c9fe-510b-4038-aeeb-547549344952
∇ = Nabla()

# ╔═╡ 82c74e52-96ad-4a49-bf77-e04058866814
LinearAlgebra.dot(v, ::Nabla) = DirDeriv(v)

# ╔═╡ a0a2f5e2-3a37-431b-bd3c-9284b3897540
LinearAlgebra.cross(::Nabla, v) = curl(v)

# ╔═╡ 85de21e2-2f76-417f-bfe2-b1234f52a0ba
LinearAlgebra.dot(::Nabla, v) = divergence(v)

# ╔═╡ 0f437155-602c-4802-9c6d-e224847da765
Δ(v) = lapl(v)

# ╔═╡ 6cf7ba1a-280d-4a32-af8b-5f8294d808ab
md"""
Derivatives are merged and comparable, this gives things like $\nabla\cdot(\nabla \times v) = 0$ for free
"""

# ╔═╡ 33cba5fc-bec8-4546-8b87-ea3263247fcb
0 == ∇⋅(∇ × u)

# ╔═╡ 26cf46a4-538f-498e-8d91-c3da69be5a09
md"""
# Integration
"""

# ╔═╡ 1a9dc7f6-9de2-41d9-a6d3-b76711cdff02
intx, inty = Integral.([x, y], 0, 2pis/kv)

# ╔═╡ 6a901902-aba7-4b0c-86c0-83d93ca78cf7
meanflow(v) = inty(intx(v))

# ╔═╡ b6d19cac-eb96-4093-992c-6317d15ced9e
eqmag = N * (∇ × (meanflow.(((B⋅∇).(u)) × u))) - lambda * (Δ.(B))

# ╔═╡ 24ed8858-e348-4691-a03a-73dab1a59bc4
md"""
# Substitution
"""

# ╔═╡ 45f9e92d-e9f6-4c67-bef2-253843545e8f
u0 = [sin(kv*x)*cos(kv*y), -cos(kv*x)*sin(kv*y), w*sin(kv*x)*sin(kv*y)]

# ╔═╡ 6c6a6c27-3053-4230-8b9e-532721d3b7f1
B1 = [cos(kB*z), sin(kB*z), 0]

# ╔═╡ 0a5a5f91-f0a8-48a0-9df6-da88cc989b93
eq0 = substitute.(eqmag, Ref(Dict([B .=> B1; u .=> u0])))

# ╔═╡ fc9814ce-9b87-4a45-bc70-01f7a62fc83f
md"""
# Rule-based term rewriting
"""

# ╔═╡ 08a1ff42-3090-4802-8cf4-27fb10cf80b6
rsin = @rule sin(~x)^2 => (1-cos(2*(~x))) / 2

# ╔═╡ 5f7ebe49-1a39-441c-aed6-c09ec20bb4ce
rcos = @rule cos(~x)^2 => (1+cos(2*(~x))) / 2

# ╔═╡ deb7c562-5600-406d-aaf1-d603553580fc
trigsimplify(x) = simplify(x, Postwalk(Chain([rcos, rsin])))

# ╔═╡ b8673b11-dae9-4851-8168-84fb3f323999
trigsimplify.(eq0)

# ╔═╡ 0f8d8e20-2f19-4ba2-a010-1d106fc04f53
SymbolicUtils.maketerm(::Type{Sympoly.Polyform}, op, args, meta) = op(args...)

# ╔═╡ Cell order:
# ╠═e6ee6b58-fa93-11ef-1964-f7002ccf43fc
# ╠═589130c5-0ae3-4a43-8ea9-5342848dd695
# ╠═7aa1e756-1683-463c-8b9e-6ef65dad5f41
# ╠═93cfd37b-3c83-4361-9773-f24ef805b8fe
# ╠═1df249b1-eff3-432d-980e-3ab2e6700d42
# ╠═b7bd4335-621e-4cb9-afab-de414b080a27
# ╠═b2ea4e74-cec7-4b06-921d-028a97cacdc1
# ╠═812ff2be-1328-4095-8423-5eb82104c720
# ╠═f37f80d7-dfea-47a2-858e-14983567056f
# ╟─a66fef1d-11a7-4b48-9764-6e5a95e6352b
# ╠═5b87a70f-3226-4a02-a06d-7802bf462bcd
# ╠═c96dba35-c3da-45a8-b982-9bf6ef7ce12b
# ╠═43a64f2e-43c9-4a96-910d-a6c518ce23af
# ╟─2be13b09-fd4b-460f-a856-fcc96a38c3dd
# ╠═8fbd807b-1f18-43f4-b74b-f543e7ea244a
# ╠═36610c34-e8db-43de-b6e2-c34b13fb5673
# ╟─32a47950-8a10-4f62-801b-aa72649a5618
# ╠═b3c6a347-f386-4694-b91b-b75bf15e5c45
# ╠═ab3bc2a6-a4d2-410e-86a1-5734c9768017
# ╠═d718fb69-4d78-4fe4-865a-9e972cd02ba8
# ╠═27283c23-df19-4131-bf96-4221388cf776
# ╠═06b36272-de6a-4a50-80c3-8b251e393008
# ╟─851e8f55-91df-47bd-b42a-63b3383e2664
# ╠═57e7f8f7-0134-4dc2-bb9c-a0743f61e910
# ╠═ce448d5d-9b34-4c6b-9fc7-b2efaea7959b
# ╠═5998c9fe-510b-4038-aeeb-547549344952
# ╠═82c74e52-96ad-4a49-bf77-e04058866814
# ╠═a0a2f5e2-3a37-431b-bd3c-9284b3897540
# ╠═85de21e2-2f76-417f-bfe2-b1234f52a0ba
# ╠═0f437155-602c-4802-9c6d-e224847da765
# ╟─6cf7ba1a-280d-4a32-af8b-5f8294d808ab
# ╠═33cba5fc-bec8-4546-8b87-ea3263247fcb
# ╟─26cf46a4-538f-498e-8d91-c3da69be5a09
# ╠═1a9dc7f6-9de2-41d9-a6d3-b76711cdff02
# ╠═6a901902-aba7-4b0c-86c0-83d93ca78cf7
# ╠═b6d19cac-eb96-4093-992c-6317d15ced9e
# ╟─24ed8858-e348-4691-a03a-73dab1a59bc4
# ╠═45f9e92d-e9f6-4c67-bef2-253843545e8f
# ╠═6c6a6c27-3053-4230-8b9e-532721d3b7f1
# ╠═0a5a5f91-f0a8-48a0-9df6-da88cc989b93
# ╟─fc9814ce-9b87-4a45-bc70-01f7a62fc83f
# ╠═b32fe487-889f-43ff-bad9-87f9cbed65f5
# ╠═a21120aa-346b-4f06-9fd0-2221564b1bd8
# ╠═08a1ff42-3090-4802-8cf4-27fb10cf80b6
# ╠═5f7ebe49-1a39-441c-aed6-c09ec20bb4ce
# ╠═deb7c562-5600-406d-aaf1-d603553580fc
# ╠═b8673b11-dae9-4851-8168-84fb3f323999
# ╠═0f8d8e20-2f19-4ba2-a010-1d106fc04f53
