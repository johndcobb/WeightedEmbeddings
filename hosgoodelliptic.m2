k = ZZ/32003
P2 = k[x,y,z]
B = ideal (x,y,z)

f = x^3+ x*y^2 + z^3


C = ideal f
g = genus C

--- check that C is smooth
J = minors_1 jacobian C
saturate(radical trim C+J, B) == (1) -- if smooth, then this is true


R = quotient C;
while euler(randp = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 20));
apply(#J, j -> stack {net ((flatten degrees ring J#j)), net betti res J#j})

res J#0
betti res J#0


C = createHyperelliptic(2)
R = quotient C;
while euler(randp = first decompose ideal random(1, R)) != 1 do ()

needsPackage "SpaceCurves"
g = 2
 d = g+3
C = curve(d,g)
R = quotient ideal C

while euler(randp = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g+2, l-> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => 20));
apply(#J, j -> stack {net ((flatten degrees ring J#j)), net betti res J#j})
res J#0
res J#2

R = sectionRing(randp, 1, "ReduceDegrees" => true, DegreeLimit => 20)


S = ambient R
I = ideal R
degrees S

basis(3, S)
basis(6,S)
basis(9,S)
basis(6, cokernel basis(3,S))
basis(9, cokernel basis(3,S))

basis(3, I)
basis(6, cokernel basis(3,I))

-- look at syzygies of veronese of polynomial ring by itself!
-- how do syzygies of veroneses of (R/I) compare to veroneses of R and I?