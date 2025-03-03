module Sympoly
using Oscar
using SymbolicUtils
import TermInterface

export @variables, Functional, substitute
include("types.jl")

using Combinatorics
using DiffRules
export derive, Derivative
include("derivatives.jl")

export integrate, Integral
include("integrals.jl")

end
