using Sympoly
using Test
using SymbolicUtils

@testset "Sympoly.jl" begin
    x, y = @variables x y

    @test !iscall(x)
    @test (/) === operation(x / y)
    @test all(arguments(x / y) .== [x, y])

    x + y
    x - y
    x*y
    x / y

    x + 1
    1 + x

    2x
    x*2

    2 / x
    x / 2

    -x

    1 - x
    x - 1

    @test isone((x/y) / (x/y))
    @test isone(((x+1) + x) / (2x+1))
    @test 2x+1 == ((((x+1) + x) / (x+1))*(x+1))
    @test y+2 == (x+2)*(y+2)/(x+2)
end
