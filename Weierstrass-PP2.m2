restart
load "WeightedEmbeddings.m2"

--- Lets compute examples of hyperelliptic and non-hyperelliptic plane curves,
-- and choose a random point vs weierstrass points.
-- Need to go to genus 3, since all genus 2 curves are hyperelliptic.

-- In genus 3, non-hyperelliptic curves are exactly nonsingular quartics in P^2.

k = ZZ/32003 -- its important that this is a BIG enough prime so that the intersection factors....
P2 = k[x,y,z]
B = ideal (x,y,z)

-- In P^2 only curves of genus = 1, 3, 6, 10, 15, ... can be smooth
f = x^4 + x*y^3 + 2*y^3*z + z^3*y + y^4 + x^2*y^2 + z^4 -- genus 3
f = 2*x^4*y + 3*x*z*y^3 + 5*x^4*z + x^3*z^2 + x^3*z*y + y^5 + z^4*y -- genus 6
C = ideal f
X = Proj quotient C
isSmooth X
g = genus X

--- check that C is smooth
jac = minors_1 jacobian C
assert( saturate(radical trim C+jac, B) == 1) -- if smooth, then this is true

-- For plane curves, the weierstrass points are given by the intersection
-- of the curve with its Hessian. Generically, there shoud be 3(6-2)*6 = 72 points.
v = matrix{{x,y,z}}; Hessian = diff(v ** transpose v, f)
weierstrass = ideal(f, det(Hessian))
pt = first decompose weierstrass
pt1 = (decompose weierstrass)#1
pt2 = (decompose weierstrass)#2
pt = intersect(pt1, pt2)

pt = (decompose weierstrass)#3
R = quotient C;
pt = promote(pt,R)

errorDepth=1
gbTrace = 0
debugLevel=1
J = apply(1..g+1, l ->
    elapsedTime ideal sectionRing(pt, l, "ReduceDegrees" => true, DegreeLimit => 100));

-- J = apply({1,2,3,4,5,7,8,9,10}, l ->
--     elapsedTime ideal sectionRing(pt, l, "ReduceDegrees" => true, DegreeLimit => 30));

p2 = apply(J, async minimalBetti);
netList toList p2

apply(#J, j -> elapsedTime stack {
	print j;
	I := J#j;
	R := ring I;
	b := minimalBetti I;
	net(regularity b - sum (flatten degrees R) + numgens R + 1),
	net flatten degrees R,
	net b})


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
