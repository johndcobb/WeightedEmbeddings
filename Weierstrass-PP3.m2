needsPackage "NormalToricVarieties"
load "WeightedEmbeddings.m2"

--- Lets compute examples of space curves of genus g and choose weierstrass points.

-- its important that the field is a BIG enough prime so that delta has some factors
kk = ZZ/32003
P1xP1 = (toricProjectiveSpace(1, CoefficientRing => kk))^**2
S0 = ring P1xP1
B0 = ideal P1xP1

P3 = toricProjectiveSpace(3, CoefficientRing => kk)
S = ring P3
B = ideal P3

-- cf. https://mathoverflow.net/questions/79546/can-any-smooth-hyperelliptic-curve-be-embedded-in-a-quadric-surface
f0 = random({2,g+1}, ring P1xP1)
R0 = quotient ideal f0
I = ker map(R0, S, {R0_1*R0_3, R0_0*R0_3, R0_1*R0_2, R0_0*R0_2}) -- ideal of C0 in P1xP1 in P^3
R = quotient I
C = Proj R
assert( g == genus C )

--- check that C is smooth
jac = minors_1 jacobian I
assert isSmooth C
assert( saturate(radical I + jac, B) == 1) -- if smooth, then this is true

-- the Weierstrass points are the ramification points of the projection to the first P1,
-- which are roots of the determinant of the Hessian matrix:
delta = det diff(matrix {S0_*_{0,1}} ** transpose matrix {S0_*_{0,1}}, f0)
-- but it's simpler this way, given by the discriminant:
(a,b,c) = toSequence flatten entries last coefficients(f0,
    Variables => S0_*_{0,1}, Monomials => {S0_0^2, S0_0*S0_1, S0_1^2})
delta = b^2 - 4*a*c
-- either way, delta is the branch divisor, which should have degree 2g+2
assert( degree delta == {0, 2*g+2} )

-- pts = decompose ker map(R0/delta, S, {x_1*R0_3, R0_0*R0_3, R0_1*R0_2, R0_0*R0_2}) -- ideal of Weierstrass locus in P1xP1 in P^3
-- pt = pts#0
-- faster:
pts = value \ toList factor delta -- the lift of the roots from P1 back to C are the Weierstrass points
pts = select(pts, f -> degree f == {0,1}) -- depends on the field
pt = ker map(R0/pts#0, S, {R0_1*R0_3, R0_0*R0_3, R0_1*R0_2, R0_0*R0_2}) -- ideal of a point in P1xP1 in P^3

pt = promote(pt, R)

while euler(randp = first decompose ideal random(1, R)) != 1 do ()

end--
restart
g = 6
load "Weierstrass-PP3.m2"

-- pick one Weierstrass point
gbTrace = 0
debugLevel = 1
J = apply(1..g+2, l ->
    elapsedTime ideal sectionRing(pt, l, "ReduceDegrees" => true, DegreeLimit => 30));

-- genus 8, l = 8 is missing in the table
p2 = apply(J, async minimalBetti);
netList toList p2
(openOutAppend "genus-6-betti-tables.m2") << horizontalJoin between_"  " apply(#J,
    j -> elapsedTime stack {
	print j;
	I := J#j;
	R := ring I;
	if not isReady p2#j then return;
	b := minimalBetti I;
	concatenate("   p = ", toString(j+1)),
	concatenate("wreg = ", toString(regularity b - sum (flatten degrees R) + numgens R + 1)),
	concatenate("degs = ", toString runLengthEncode flatten degrees R),
	net b}) << endl << flush << close



while euler(randp = first decompose ideal random(1, R)) != 1 do ()

elapsedTime J = apply(1 .. 2*g+2, l -> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 27));
elapsedTime J = apply({1,2,3,4,5,6,7,-*8,*-9,10,11,12,13}, l -> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 27));
apply(#J, j -> elapsedTime stack {
	print j;
	I := J#j;
	R := ring I;
	b := minimalBetti I;
	net(regularity b - sum (flatten degrees R) + numgens R + 1),
	net ((j+1)*(flatten degrees R)),
	net b})

allowableThreads = 7
needs "threads.m2"
T = schedule(() -> apply(6, async(i -> (res J#i; print i))))


syz mingens J#5
netList apply(12, i -> { i, runLengthEncode last degrees mingens J#i, runLengthEncode last degrees gens J#i })

j=0
regularity res J#j - sum (flatten degrees ring J#j) + numgens ring J#j + 1
ring J#0
basis(7, quotient J#0)
degrees basis(7, quotient J#0)
degrees ring J#0
J#6

basis(14, quotient J#0)
J#6
