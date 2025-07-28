--------------------------------------------------------------------------------
--- computing examples of section rings of not-very-ample divisors on curves ---
--------------------------------------------------------------------------------
restart
path = prepend("/Users/John/Documents/GitHub/WeightedEmbeddings/code", path)
loadPackage("SectionRing")
needsPackage "SpaceCurves"
 
 --random genus g curve
 g = 4
 d = g+3
 C = curve(d,g)
 R = quotient ideal C;
 while euler(I = first decompose ideal random(1, R)) != 1 do ()
 J = apply(1 .. 2*g+2, l-> ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true));
 apply(#J, j -> stack {net ((j+1)*(flatten degrees ring J#j)), net betti res J#j})

-- mahrud: Can build up C from graded parts, but need to be doing it over the standard grading
needsPackage "Complexes"
part_3 complex C
part_6 complex C
part_9 complex C

needsPackage "Complexes"
--- hyperelliptic  genus 10 curve

S = ZZ/32003[x,y,z]
g = 2
C = ideal(y^2*z^(2*g) - x^(2*g+2))
R = quotient C

--- this intersects C with a random linear form, and then takes one of the components p of the intersection. It then makes sure that h^0(p) = 1, so that its not a double point.
while euler(I = first decompose ideal random(1, R)) != 1 do ()
J = apply(1 .. 2*g, l-> ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true));
--apply(J, j -> stack {net flatten degrees ring j, net betti res j})
apply(J, j -> flatten degrees ring j)
-- THIS IS NOT RIGHT!!! Should be very ample at 2g-1


--- ways to create a hyperelliptic curve:
--- https://mathoverflow.net/questions/79546/can-any-smooth-hyperelliptic-curve-be-embedded-in-a-quadric-surface

-- I have made a function that will generate hyperelliptic curves of genus g based off of Jay's function. Its in WeightedEmbeddings.m2.
restart
load "WeightedEmbeddings.m2"
g = 3
C = createHyperelliptic(3)

S = ring C;
B = ideal flatten entries vars S;
saturate(radical trim (C+ minors_1 jacobian C),B ) == ideal (1_S) -- its smooth

3 == genus(C) -- its has genus g
dim(C)-1 == 1 -- C is a curve

-- now we can compute the section ring
R = quotient C

-- while euler(I = first decompose ideal random(1, R)) != 1 do ()

I = first decompose ideal random(1, R) -- every plane I choose contains the curve....
basis(1,C) -- but I cant find any linear forms vanishing on C.

-- my issue is this is not the equation of a point....
J = apply(1 .. 2*g, l-> ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true));
 --apply(J, j -> stack {net flatten degrees ring j, net betti res j})
apply(J, j -> flatten degrees ring j)


------ smooth plane quartic (non-hyperelliptic)
R' = ZZ/3[x_0,x_1,x_2]
f' = (flatten entries random(R'^1,R'^{-4}))_0
R = ZZ/32003[x_0,x_1,x_2]
phi = map(R,R'); f = phi(f');
C = ideal f;
-- make sure its smooth
J = minors_1 jacobian C
B = ideal flatten entries vars R
saturate(radical trim J, B) == (1) -- if smooth, then this is true


-- Here is a random point
while euler(p = first decompose ideal random(1, R)) != 1 do ()
g = genus C
J = apply(1 .. 2*g+2, l-> ideal sectionRing(p, l, DegreeLimit => 20, "ReduceDegrees" => true));
apply(J, j -> stack {net flatten degrees ring j, net betti res j}) -- this is really really slow?