restart
loadPackage("SectionRing")
topLevelMode = Standard

--- Lets compute examples of hyperelliptic and non-hyperelliptic plane curves, and choose a random point vs weierstrass points.
-- Need to go to genus 3, since all genus 2 curves are hyperelliptic.

-- In genus 3, nonhyperelliptic curves are exactly nonsingular quartics in P^2.

k = ZZ/32003 -- its important that this is a BIG enough prime so that the intersection factors....
P2 = k[x,y,z]
B = ideal (x,y,z)

f = x^4 + x*y^3 + 2*y^3*z + z^3*y + y^4 + x^2*y^2 + z^4
g = 3
C = ideal f

--- check that C is smooth
J = minors_1 jacobian C
assert(saturate(radical trim C+J, B) == 1) -- if smooth, then this is true

-- For plane curves, the weierstrass points are given by the intersection of the curve with its Hessian. Generically, there shoud be 3(4-2)*4 = 24 points.
v = matrix{{x,y,z}}; Hessian = diff(v ** transpose v, f)
weierstrass = ideal(f, det(Hessian))
pt = trim first decompose(weierstrass)
assert(euler pt == 1) -- this is a point, not a double point

R = quotient C;
pt = trim promote(pt,R)
J = apply(1 .. 2*g+2, l-> ideal sectionRing(pt, l, "ReduceDegrees" => true, DegreeLimit => 4*g+4));
apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})
res J#0
stack {net ((0+1)*(flatten degrees ring J#0)), net betti res J#0}

while euler(randp = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 4*g+4));
apply(#J, j -> stack {net ((flatten degrees ring J#j)), net betti res J#j})
apply(#J, j -> regularity J#j)
apply(#J, j -> sum flatten degrees ring J#j - numgens ring J#j)
apply(#J, j -> regularity J#j - sum (flatten degrees ring J#j) + numgens ring J#j) --- this is some sort of weighted regularity
peek (betti res J#0)
regularity J#0

--- Now, I'm going to try to use random degree d divisors D

randpts = for i from 1 to 2*g+2 list (
    while euler(randp = first decompose ideal random(1, R)) != 1 do ();
    randp
) 
D = d -> product randpts_{0..d-1}

euler(D(2))

sectionRing(D(2),"ReduceDegrees" => true, DegreeLimit => 40)

J = apply(1 .. 2*g+2, l-> ideal sectionRing(D(l), "ReduceDegrees" => true, DegreeLimit => 4*g+4)); -- this is too slow!


------------ Now lets try a hyperelliptic curve.

use P2;

f = 2*x^4*y + 3*x*z*y^3 + 5*x^4*z + x^3*z^2 + x^3*z*y + y^5 + z^4*y
g = floor((4*3)/2)
C = ideal f

--- check that C is smooth
J = minors_1 jacobian C
saturate(radical trim C+J, B) == (1) -- if smooth, then this is true

-- For plane curves, the weierstrass points are given by the intersection of the curve with its Hessian. Generically, there shoud be 3(6-2)*6 = 72 points.
v = matrix{{x,y,z}}; Hessian = diff(v ** transpose v, f)
weierstrass = ideal(f, det(Hessian))
pt = first decompose weierstrass

R = quotient C;
pt = promote(pt,R)
J = apply(1 .. 2*g+2, l-> ideal sectionRing(pt, l, "ReduceDegrees" => true));
apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})


while euler(randp = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 27));
apply(#J, j -> stack { print j;
    net(regularity res J#j - sum (flatten degrees ring J#j) + numgens ring J#j + 1),
    net ((j+1)*(flatten degrees ring J#j)), 
    net betti res J#j}) 
apply(#J, j -> (
    print(j);
    regularity res J#j - sum (flatten degrees ring J#j) + numgens ring J#j + 1)
)
j=0
regularity res J#j - sum (flatten degrees ring J#j) + numgens ring J#j + 1
ring J#0
basis(7, quotient J#0)
degrees basis(7, quotient J#0)
degrees ring J#0
J#6

basis(14, quotient J#0)
J#6