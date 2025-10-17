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
needsPackage "Depth"

kk = ZZ/32003

weightedRegularity = I -> regularity minimalBetti I - (sum flatten degrees ring I - numgens ring I)

-- FIXME: only correct for Cohen-Macaulay curves
koszulRegularity' = I -> (
    S := ring I;
    bt := minimalBetti I;
    depthM := 2; -- depth comodule I;
    wsup := flatten for i from 0 to numgens S list sum take(degrees S, -i);
    maxBeta := for i to pdim bt list max \\ last \ select(keys bt, (ind, deg, d) -> i == ind);
    max for i from 1 to pdim bt list maxBeta_i + 1 - wsup#(i+depthM) + wsup#(depthM-1))

-- TODO: use https://mathoverflow.net/questions/79546/can-any-smooth-hyperelliptic-curve-be-embedded-in-a-quadric-surface
-- to embed in P1xP1 instead
createHyperelliptic = method()
createHyperelliptic ZZ := Ideal => g -> createHyperelliptic(kk, g)
createHyperelliptic(Ring, ZZ) := Ideal => (kk, g) -> (
    degR := 2*g+2;
    F := hirzebruchSurface(g+1,
	CoefficientRing => kk);
    S := ring F;

    -- Now the equation of a hyperelliptic curve can be written as y^2 = p(x),
    -- where p is a degree degR polynomial with 2g+2 roots (those are the branch points).
    -- p is a degR polynomial at 8 branch points x=1...8 , in the O_(P^1) factor;
    p := product(degR, i -> S_0 - random kk * S_2);

    C := ideal(S_3^2 - S_1^2*p);

    -- embed the Hirzebruch by the (1,1) divisor
    B := basis({1,1}, S);
    n := numcols B - 1;
    Y := toricProjectiveSpace(n,
	CoefficientRing => kk);
    R := ring Y;
    f := map(S, R, B);
    assert(isWellDefined f);
    -- If I is the ideal for a subvariety of the hirzebruch,
    -- this gives the ideal for the embedding into the P^N
    preimage (f, C))

saveBetti = method()
saveBetti(List, String, String) := () => (B, filename, pwd) -> (
    (pwd | filename) << toExternalString(B) << close;
)
saveBetti(List,  String) := () => (B, filename) -> (
    pwd := currentDirectory() | "cache/";
    saveBetti(B, filename, pwd);
)

loadBetti = method()
loadBetti(String, String) := List => (filename, pwd) -> (
    value get (pwd | filename)
)
loadBetti(String) := List => filename -> (
    pwd := currentDirectory() | "cache/";
    loadBetti(filename, pwd)
)

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
<< apply(#J, j -> stack {
	print j;
	I := J#j;
	S' := ring I;
	"w-reg: " | elapsedTime net weightedRegularity I,
	"k-reg: " | elapsedTime net koszulRegularity' I,
	--"isCM:  " | net isCM quotient I,
	net ((j+1)*(flatten degrees ring I)),
	netList {
	    minimalBetti (map(S', S', apply(gens S', g -> if degree g < {3} then 0 else g))) I,
	    minimalBetti I}})

I = J#7;
C = res I;
minimalBetti I
L = {
    submatrixByDegrees(C.dd_1, ({0},{0}), ({3},{3})),
    submatrixByDegrees(C.dd_2, ({3},{3}), ({5},{5})),
    submatrixByDegrees(C.dd_3, ({5},{5}), ({7},{7})),
    submatrixByDegrees(C.dd_4, ({7},{7}), ({9},{9})),
    submatrixByDegrees(C.dd_5, ({9},{9}), ({11},{11})),
    submatrixByDegrees(C.dd_6, ({11},{11}), ({13},{13}))
    };
L' = {
    submatrixByDegrees(C.dd_1, ({0},{0}), ({4},{4})),
    submatrixByDegrees(C.dd_2, ({4},{4}), ({6},{6})),
    submatrixByDegrees(C.dd_3, ({6},{6}), ({8},{8})),
    submatrixByDegrees(C.dd_4, ({8},{8}), ({10},{10})),
    submatrixByDegrees(C.dd_5, ({10},{10}), ({12},{12})),
    submatrixByDegrees(C.dd_6, ({12},{12}), ({14},{14}))
    };
prune HH complex L
prune HH_1 complex L'




S = kk[x,y,z]
R = S/f
R = S/(y^2*z^3 - x^5 - x^2*y*z^2)
g = genus R
euler Proj R

elapsedTime J = apply(1 .. 2*g+2,
    l -> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => limit));
printWidth = 0
<< apply(10, j -> stack {
	print j;
	elapsedTime net weightedRegularity J#j,
	net ((j+1)*(flatten degrees ring J#j)),
	net minimalBetti J#j})
