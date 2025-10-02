-- Since C is hyperelliptic, it is a double cover of P^1. So by Riemann-Hurwitz, the degree of the ramification locus is deg(R) = 2g + 2
-- (*) ANY hyperelliptic curve of genus g embeds into the hirzebruch surface F_(g+1).

-* Explanation of (*)
-- How? Well, let pi: C --> P^1 be the hyperelliptic covering. pi_*(O_C) must be a dim 2 vector bundle on P^1, and so decomposes as a sum of line bundles O_P^1(a) + O_P^1(b).
-- Using the euler characteristic, 1-g = chi(O_P^1(a)) + chi(O_P^1(b)) = 1 + a + 1 + b. So g = -1-a-b.
-- But by kunneth formula, H^0(O_C) = H^0(O_P^1(a)) + H^0(O_P^1(b)), so dim(H^0(O_P^1(a))) + dim(H^0(O_P^1(b))). Therefore a = 0 and b < 0.
-- So can solve for b = -g-1. 
-- So pi_*(O_C) = O_P^1 + O_P^1(-g-1).
-- But now there is a surjective morphism pi^*(O_P^1 + O_P^1(-g-1)) --> O_C
-- This gives a map C -> P(O_P^1 + O_P^1(-g-1)) = F_(g+1)
*- 

needsPackage "NormalToricVarieties"
needsPackage "SectionRing"

kk = ZZ/32003

weightedRegularity = I -> regularity res I + 1 - sum flatten degrees ring I + numgens ring I

-- TODO: use https://mathoverflow.net/questions/79546/can-any-smooth-hyperelliptic-curve-be-embedded-in-a-quadric-surface
-- to embed in P1xP1 instead
createHyperelliptic = method()
createHyperelliptic ZZ := Ideal => g -> createHyperelliptic(kk, g)
createHyperelliptic(Ring, ZZ) := Ideal => (kk, g) -> (
    degR := 2*g+2;
    F := hirzebruchSurface(g+1, CoefficientRing => kk);
    S := ring F;

    -- Now the equation of a hyperelliptic curve can be written as y^2 = p(x),
    -- where p is a degree degR polynomial with 2g+2 roots (those are the branch points).
    -- p is a degR polynomial at 8 branch points x=1...8 , in the O_(P^1) factor;
    p := product(for i from 1 to degR list (S_0 - random(1,20)*S_2));

    C := ideal(S_3^2 - S_1^2*p);

    --embed the Hirzebruch by the (1,1) divisor
    b := basis({1,1},S);
    Y := toricProjectiveSpace(numColumns b - 1, CoefficientRing => kk);
    R := ring Y;
    B := ideal Y;
    f := map(S,R,b);
    assert(isWellDefined f);
    --If I is the ideal for a subvariety of the hirzebruch, this gives the ideal for the embedding
    --into the P^N
    C' := preimage (f,C);
    C')

end--
restart
needs "WeightedEmbeddings.m2"

g = 4
I0 = createHyperelliptic(ZZ/101, g)
R0 = quotient I0

while euler(randp = first decompose ideal random(1, R0)) != 1 do ()
R = sectionRing(randp, 2*g+2, "ReduceDegrees" => true)

while euler(randp = first decompose ideal random(1, R)) != 1 do ()
limit = 2 * first max degrees sectionRing(randp, 1, "ReduceDegrees" => true) + 2

elapsedTime J = apply(1 .. 2*g+2,
    l -> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => limit));
printWidth = 0
apply(#J, j -> stack {
	print j;
	elapsedTime net weightedRegularity J#j,
	net ((j+1)*(flatten degrees ring J#j)),
	net betti res J#j})
