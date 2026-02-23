load "WeightedEmbeddings.m2"
topLevelMode = Standard
--- here is a random genus 4 degree 7 curve in P^4
B = loadBetti("randomgenus4curve.m2")

-- I hope to find semigroup algebras with the same betti table, hopefully because they are  initial ideals of R(C,d)

--- For example, we fully understand d=1:

needsPackage "MonomialAlgebras"

--- Since P is general on C, the weierstrass semigroup is 
-- H(P) = <0> U <5, 6, 7, 8, 9>
-- (in general, its <0> U <g+1,...,2g+1>)

L = {5,6,7,8,9}
betti res binomialIdeal monomialAlgebra(ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees => L])
B_0
-- these betti tables are the same.

--- Here is an equivalent way to write the semigroup algebra, Gamma_1
L = {{1,0}, {5,5}, {6,6}, {7,7}, {8,8}, {9,9}}
betti res binomialIdeal monomialAlgebra(L)
B_0

---- Now, I try general d
d = 7
H = {5,6,7,8,9} -- weierstrass generating set
L = minimalAdditiveGeneratingSet for i from 5 to max(H)*4 list {ceiling(i/d),i}
-- in general, will need make a function that uses the possible sums from H.
betti res binomialIdeal monomialAlgebra(L)
R = ring binomialIdeal monomialAlgebra(L)
(flatten entries vars R) / degree
B_(d-1)
--- hmmm its totally possible that this is the initial algebra. 

-- it looks like this may be the same as the associated graded of the section ring, but that there may not be a bound like I want since these betti tables are resolved over different rings.

-- there is a choice of a subsemigroup of Gamma_d so that the bounds and stuff are apparent...

-- its certainly related...

needsPackage "SpaceCurves"
 g = 7
 d = g+3
 C = curve(d,g)
 R = quotient ideal C;
 while euler(I = first decompose ideal random(1, R)) != 1 do ()
 J = apply(1 .. 2*g+2, l-> ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true));

flatten((flatten entries vars ring J_1) / degree)