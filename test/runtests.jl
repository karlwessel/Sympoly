using Sympoly
using Test
import SymbolicUtils: substitute, arguments, operation, iscall, @rule
import SymbolicUtils.Rewriters: Postwalk, PassThrough, Prewalk
import Nemo: QQ
import Sympoly: Polyform, tonumber, isderived, occursin, docleanup, makebase, makeop

x, y = @variables x y
@testset "Sympoly.jl" begin
    @test 1 // 2 == tonumber(QQ(1 // 2))
    @test 3 == tonumber(QQ(3 // 1))
    @test !iscall(x)
    @test iscall(x / y)
    @test iscall(im*x)
    @test (//) === operation(x / y)
    @test all(arguments(x / y) .== [x, y])

    @test zero(x) isa Polyform
    @test zero(x) == 0
    @test one(x) isa Polyform
    @test one(x) == 1

    @test x + y isa Polyform
    @test x - y isa Polyform
    @test x * y isa Polyform
    @test x / y isa Rational{Polyform}

    @test x + 1 isa Polyform
    @test 1 + x isa Polyform

    @test 2x isa Polyform
    @test x*2 isa Polyform

    @test 2 / x isa Rational{Polyform}
    @test x / 2 isa Rational{Polyform}

    @test x/y + y == (x + y^2)/y
    @test x/y * y == x
    @test x/y - y == (x - y^2)/y
    @test x/2/pi == x/pi/2

    @test -x isa Polyform

    @test 1 - x isa Polyform
    @test x - 1 isa Polyform

    @test isone((x/y) / (x/y))
    @test isone(((x+1) + x) / (2x+1))
    @test 2x+1 == ((((x+1) + x) / (x+1))*(x+1))
    @test y+2 == (x+2)*(y+2)/(x+2)

    @test repr(2x/4y) == "(x / 2*y)"
    @test repr(2/4y) == "(1 / 2*y)"
    @test repr(2x/4) == "(x / 2)"
    
    @test sin(x) isa Polyform
    @test atan(x, y) isa Polyform
    @test sin(x/pi) isa Polyform
    @test_broken sin(im*x) isa Complex{Polyform}
    @test_broken tan(im*x) isa Complex{Polyform}
    @test atan(x, y) isa Polyform
    @test atan(x/pi, y) isa Polyform
    
    @test x == Sympoly.cleanup(x)
    @test sin(x) == Sympoly.cleanup(sin(x))
    @test (sin(x)*x/sin(x)) == x
    @test isempty(docleanup(numerator(sin(x)*x/sin(x))).fns)

    f = Functional(:f)
    @test f(x) isa Polyform
end

@testset "TermInterface" begin
    @test !iscall(Polyform(0))
    @test !iscall(x-x)


    
    @test 3 == substitute((x+1).p, x.p => 2)
    @test 7//3 == substitute((2x+1).p, x.p => 2//3)
    @test 7 == substitute((y*(2x+1)).p, x.p => 2//3, y.p => 3)

    @test 2 == substitute(x/pi, x => 2*Polyform(pi))
    @test 2im == substitute(im*x, x => 2)

    @test ((x^2 + y) * (x^2 + 2)) == substitute(((x + y) * (x + 2)), Dict([x => x^2]))
    @test ((2 + y) * 4) == substitute(((x + y) * (x + 2)), Dict([x => 2]))

    @test x + 1 == substitute(sin(x) + 1, sin(x) => x)
    @test 3 == substitute(sin(x) + 1, sin(x) => 2)
    @test isequal(substitute(x + sin(x) + sin(sin(x + 1)), x => Polyform(1)), 1 + sin(Polyform(1)) + sin(sin(Polyform(2))))
    @test sin(2y) + sin(sin(2y)) + sin(sin(sin(2y) + 1)) ==
      substitute(x + sin(x) + sin(sin(x + 1)), x => sin(2y))

    f = Functional(:f)
    @test operation(derive(f(x), x)) isa Derivative
    @test substitute(derive(f(x), x), x => y) == derive(f(y), y)
    @test substitute(integrate(f(x), x, 0, 1), x => y) == integrate(f(y), y, 0, 1)
    @test substitute(integrate(f(x), x, y, 1), y => 0) == integrate(f(x), x, 0, 1)

    @test y + 2 == substitute(f(x) + y, f(x) => 2)
    @test y + f(2) == substitute(f(x) + y, x => 2)

    r = @rule sin(~x)^2 => (1 - cos(2(~x))) / 2
    @test Postwalk(PassThrough(r))(2+sin(2x)^2) == (1 - cos(4x)) / 2 + 2
    # test for rational
    @test Postwalk(PassThrough(r))(2+sin(2x)^2/x) == (1 - cos(4x)) / 2x + 2
end

@testset "Makeconst" begin
    @test 2 == makebase(Polyform(2))
    @test pi == makebase(Polyform(pi))
    @test 2pi == makebase(2*Polyform(pi))
    @test 2 == makebase((makeop(cos, 0)+1))
    @test 3 == makebase((2*makeop(cos, 2*Polyform(pi))+1))
    
    @test sin(4*Polyform(pi)) == 0
end

@testset "derivatives" begin
    f = Functional(:f)

    @test occursin(2x, 2x)
    @test occursin((2x).p, (2x).p)

    @test isderived(x)
    @test !isderived(derive(f(x), x))
    @test isderived(sin(x))

    @test 0 == derive(Polyform(2), x)
    @test 0 == derive(Polyform(pi), x)

    @test x+pi isa Polyform

    @test 2(x+1) + y - 2 == derive((x+1)^2 + (y-2)*(x), x)
    @test derive(sin(x), x) == cos(x)
    @test derive(sin(y), x) == 0
    @test derive(identity(2x), x) == 2

    # rational created by derivative
    @test derive(sin(x/pi), x) == cos(x/pi) / pi

    @test derive(sin(2x), 2x) == cos(2x)

    @test "$(derive(x/y, x))" == "(1 / y)"

    @test derive(f(x,y),x) isa Polyform

    @test iszero(derive(f(y), x))
    @test iszero(derive(derive(f(x), y), x))
    @test iszero(derive(derive(f(x,y), x), y) - derive(derive(f(x,y), y), x))

    @test x*cos(x) + sin(x) == substitute(derive(x*f(x), x), f(x) => sin(x))
    # derivative returns a rational
    @test substitute(derive(derive(f(x, y), x), y), f(x, y) => sin(x/pi)*cos(y/pi)) == -cos(x/pi)*sin(y/pi)/pi/pi

    @test 4cos(2x)*sin(2x) + 4sin(2x)*cos(2x) + 8x*cos(2x)*cos(2x) - 8x*sin(2x)*sin(2x) - 4sin(2x) == derive(derive(x+x*sin(2x)^2 + sin(2x), x), x)
    @test 1 + sin(2x)^2 + x*4*sin(2x)*cos(2x) + 2cos(2x) == derive(x+x*sin(2x)^2 + sin(2x), x)

    Dx, Dy = Derivative.([x, y])
    @test -y^2*sin(x*y) == substitute(Dx(Dx(f(x))), f(x) => sin(y*x))
end

@testset "integral" begin
    @test !occursin(2, x)
    @test occursin(x, x)
    @test !occursin(y, x)
    @test occursin(sin(x), x)
    @test !occursin(sin(y), x)
    @test occursin(sin(x/pi), x)

    @test 2 == integrate(x, x, 0, 2)
    @test 2y == integrate(y, x, 0, 2)
    @test 2y == integrate(y*sinpi(x/pi), x, 0, pi)
    @test iszero(integrate(sinpi(x/pi), x, 0, 2*Polyform(pi)))
    @test 2sin(y) + 4 == integrate(sin(y)+2, x, 0, 2)
    @test 2y + 2 == integrate(x + y, x, 0, 2)
    @test iszero(integrate(sinpi(2x/pi), x, 0, pi))
    @test 2 == integrate(cos((1//2)*x), x, 0, pi)
    @test 2/y == integrate(sinpi(x/pi)/y, x, 0, pi)

    @test 2/y == integrate(sinpi(x/pi)/y, x, 0, pi)
    @test 2 == integrate(cospi((1//2)*x/pi), x, Polyform(0), Polyform(pi))

    a, b = @variables a b
    f = Functional(:f)
    @test integrate(derive(f(x), x), x, a, b) == f(b) - f(a)
    @test integrate(derive(cospi(x), x), x, a, b) == cospi(b) - cospi(a)
    @test integrate(derive(sinpi(x), x), x, a, b) == sinpi(b) - sinpi(a)

    @test derive(integrate(f(x), x, 0, 1), x) == 0
    @test derive(integrate(f(x), x, 0, x), x) != 0

    @test ((1 - cospi(2*a/pi)) / y) == integrate(sinpi(y*x/pi), x, 0, 2a/y)

    @test repr(integrate(sin(x)*x, x, 0, 1)) == "∫dx[0 to 1](x*sin(x))"
    @test repr(integrate(f(x), x, 0, 1)) == "∫dx[0 to 1](f(x))"
end

@testset "inspection" begin
    inspect(x)
    inspect(x/y)
    inspect((x+y)/x)
end
