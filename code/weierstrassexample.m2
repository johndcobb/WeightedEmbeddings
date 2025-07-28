restart
path = prepend("/Users/John/Documents/GitHub/WeightedEmbeddings/code", path)
loadPackage("SectionRing")

--- Lets compute examples of hyperelliptic and non-hyperelliptic plane curves, and choose a random point vs weierstrass points.
-- Need to go to genus 3, since all genus 2 curves are hyperelliptic.

-- In genus 3, nonhyperelliptic curves are exactly nonsingular quartics in P^2.

k = ZZ/10000019 -- its important that this is a BIG enough prime so that the intersection factors....
P2 = k[x,y,z]
B = ideal (x,y,z)

f = x^4 + x*y^3 + 2*y^3*z + z^3*y + y^4 + x^2*y^2 + z^4
g = 3
C = ideal f

--- check that C is smooth
J = minors_1 jacobian C
saturate(radical trim C+J, B) == (1) -- if smooth, then this is true


-- For plane curves, the weierstrass points are given by the intersection of the curve with its Hessian. Generically, there shoud be 3(4-2)*4 = 24 points.
v = matrix{{x,y,z}}; Hessian = diff(v ** transpose v, f)
weierstrass = ideal(f, det(Hessian))
pt = first decompose(weierstrass)
euler(pt) == 1 -- this is a point, not a double point

R = quotient C;
pt = promote(pt,R)
J = apply(1 .. 2*g+2, l-> ideal sectionRing(pt, l, "ReduceDegrees" => true));
apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})


while euler(randp = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true));
apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})

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
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true));
apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})

