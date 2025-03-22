module Sympoly
using Nemo
import Nemo: exponent_vector!
using SymbolicUtils
import TermInterface

export @variables, Functional, substitute, Polyform
include("types.jl")

using Combinatorics
using DiffRules
export derive, Derivative
include("derivatives.jl")

export integrate, Integral
include("integrals.jl")

export inspect
include("inspection.jl")
end
