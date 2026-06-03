newPackage(
    "WeightedEmbeddings",
    Date => "May 31, 2026",
    Version => "0.1",
    Headline => "embeddings of curves in weighted projective spaces",
    Authors => {
	{ Name => "Maya Banks",     Email => "mayadb@uic.edu",       HomePage => "https://sites.google.com/view/mayabanks" },
	{ Name => "John Cobb",      Email => "john.cobb@auburn.edu", HomePage => "https://johndcobb.github.io"},
	{ Name => "Mahrud Sayrafi", Email => "mahrud@mcmaster.ca",   HomePage => "https://mahrud.github.io" }
	},
    PackageExports => { "SectionRing", "NumericalSemigroups", "NormalToricVarieties" },
    Keywords => { "Commutative Algebra", "Algebraic Geometry" },
    DebuggingMode => true
    )

export {
    "createHyperelliptic",
    "minimalAdditiveGeneratingSet",
    "numericalSemigroupGenerators",
    "weightedRegularity",
    "koszulRegularity'",
    }

-- TODO: fix in Complexes, for modules too
minimalBetti Ideal := BettiTally => opts -> I -> I.cache.minimalBetti ??= minimalBetti(comodule I, opts)

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

weightedRegularity = I -> regularity minimalBetti I - (sum flatten degrees ring I - numgens ring I)

-- FIXME: only correct for Cohen-Macaulay curves
koszulRegularity' = I -> (
    S := ring I;
    bt := minimalBetti I;
    depthM := 2; -- depth comodule I;
    wsup := flatten for i from 0 to numgens S list sum take(degrees S, -i);
    maxBeta := for i to pdim bt list max \\ last \ select(keys bt, (ind, deg, d) -> i == ind);
    max for i from 1 to pdim bt list maxBeta_i + 1 - wsup#(i+depthM) + wsup#(depthM-1))

kk := ZZ/32003

-- TODO: in Weierstrass-PP3.m2 I do this with curves in P1xP1, should this be a separate function?
-- I didn't do this yet because I needed some internal data to get the Weierstrass points
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

-- Return a minimal additive generating subset of a given list of pairs {a,b}
minimalAdditiveGeneratingSet = (L) -> (
    L = unique L;

    -- sort by (a+b), then a, then b
    L = sort(L, u -> {u#0+u#1, u#0, u#1});

    maxA := max apply(L, u -> u#0);
    maxB := max apply(L, u -> u#1);

    -- reachable = all sums of chosen generators, but only within the bounding box
    reachable := new MutableHashTable;
    reachable#{0,0} = true;

    addGen := (g) -> (
	a := g#0; b := g#1;
	if (a==0 and b==0) then return;

	keysList := keys reachable; -- snapshot
	for p in keysList do (
	    x0 := p#0; y0 := p#1;
	    k := 1;
	    while (x0 + k*a <= maxA and y0 + k*b <= maxB) do (
		reachable#{x0 + k*a, y0 + k*b} = true;
		k = k+1;
		);
	    );
	);

    G := {};
    for v in L do (
	if not reachable#?v then (
	    G = append(G, v);
	    addGen(v);
	    );
	);

    G)

-- not quite ideal yet
numericalSemigroupGenerators = hf -> (
    -- numerical semigroup elements so far
    SG := new MutableList;
    SG#0 = true;
    --
    inSG := (n, G) -> SG#?n and SG#n === true or (
	for i to n do (
	    if SG#?i and SG#i === true then for g in G do (
		if i+g <= n then SG#(i+g) = true;
		);
	    );
	SG#?n and SG#n === true
	);
    -- numegrical semigroup generators
    G := new MutableList;
    mult := infinity;
    streak := 0;
    --
    n := 0;
    prev := hf n;
    while streak < mult do (
	n += 1;
	cur := hf n;
	jump := cur - prev;
	if jump == 0 then streak = 0 else
	if jump == 1 then (
	    mult = min(mult, n); -- FIXME: find this earlier?
	    if not inSG(n, G) then G##G = n;
	    streak = streak + 1)
	else error "expected jumps of at most 1";
	prev = cur);
    toList G)

saveBetti = method()
saveBetti(List, String, String) := () => (B, filename, pwd) -> (
    (pwd | filename) << toExternalString(B) << close)

saveBetti(List,  String) := () => (B, filename) -> (
    saveBetti(B, filename, currentDirectory() | "cache/"))

loadBetti = method()
loadBetti(String, String) := List => (filename, pwd) -> (
    value get(pwd | filename))

loadBetti String := List => filename -> (
    loadBetti(filename, currentDirectory() | "cache/"))


beginDocumentation()

doc ///
Node
  Key
    WeightedEmbeddings
  Headline
    embeddings of curves in weighted projective spaces
  Description
    Text
      This package contains helper routines for constructing examples of
      embedded hyperelliptic curves and for measuring regularity from their
      Betti tables in weighted polynomial rings.
    Tree
      :Constructing examples
       > createHyperelliptic
      :Regularity computations
       > weightedRegularity
       > koszulRegularity'
      :Semigroup utilities
       > minimalAdditiveGeneratingSet

Node
  Key
    createHyperelliptic
   (createHyperelliptic, ZZ)
   (createHyperelliptic, Ring, ZZ)
  Headline
    construct a projective model of a hyperelliptic curve
  Usage
    createHyperelliptic g
    createHyperelliptic(kk,g)
  Inputs
    g:ZZ
      the genus
    kk:Ring
      the coefficient ring
  Outputs
    :Ideal
      the ideal of a random hyperelliptic curve embedded in projective space
  Description
    Text
      Constructs a genus $g$ hyperelliptic curve as a divisor on the Hirzebruch
      surface $F_{g+1}$ and then embeds the surface by the divisor of bidegree
      $(1,1)$.  If no coefficient ring is supplied, the finite field
      @TT "ZZ/32003"@ is used internally.

Node
  Key
    weightedRegularity
  Headline
    compute a weighted regularity from a minimal Betti table
  Usage
    weightedRegularity I
  Inputs
    I:Ideal
      an ideal in a weighted polynomial ring
  Outputs
    :ZZ
      the regularity of the minimal Betti table, shifted by the ambient weights
  Description
    Text
      Computes @TO regularity@ of the cached minimal Betti table of @TT "I"@
      and subtracts the sum of the variable degrees minus the number of
      variables of the ambient ring.

Node
  Key
    koszulRegularity'
  Headline
    estimate Koszul regularity for a Cohen-Macaulay curve
  Usage
    koszulRegularity' I
  Inputs
    I:Ideal
      an ideal defining a Cohen-Macaulay curve
  Outputs
    :ZZ
      the computed Koszul regularity estimate
  Description
    Text
      Computes the regularity expression used in the weighted-embedding
      experiments from the minimal Betti table of @TT "I"@.  The current
      implementation assumes the quotient is a Cohen-Macaulay curve.

Node
  Key
    minimalAdditiveGeneratingSet
  Headline
    find a minimal additive generating subset of lattice points
  Usage
    minimalAdditiveGeneratingSet L
  Inputs
    L:List
      a list of pairs @TT "{a,b}"@
  Outputs
    :List
      a minimal subset of @TT "L"@ that additively generates the points of
      @TT "L"@ inside the bounding box determined by @TT "L"@
  Description
    Text
      Sorts the input pairs by total degree and keeps a point exactly when it
      is not already reachable as a nonnegative additive combination of the
      previously kept points, restricted to the coordinate bounds of the input.
      For example, @TT "minimalAdditiveGeneratingSet {{1,0},{0,1},{1,1}}"@
      returns @TT "{{0,1},{1,0}}"@.
///

end--

restart
needsPackage "WeightedEmbeddings"

kk = ZZ/32003

g = 6
I0 = createHyperelliptic(ZZ/101, g)
R0 = quotient I0

notify = true
errorDepth=1
debugLevel=1
while euler(randp = first decompose ideal random(1, R0)) != 1 do ()
R = sectionRing(randp, 2*g+2, "ReduceDegrees" => true)
R = sectionRing(randp, 1, "ReduceDegrees" => true) -- get embedding in weighted projective plane

C = Proj R

while euler sheaf comodule(randp = first decompose ideal random(1, R)) != 1 do ()
limit = 2 * first max degrees sectionRing(randp, 1, "ReduceDegrees" => true) + 2

elapsedTime J = apply(1 .. 2*g+2,
    l -> ideal sectionRing(randp, l, "ReduceDegrees" => true, DegreeLimit => limit));
printWidth = 0
<< horizontalJoin between_"  " apply(#J, j -> stack {
	print j;
	I := J#j;
	S' := ring I;
	"w-reg: " | elapsedTime net weightedRegularity I,
	"k-reg: " | elapsedTime net koszulRegularity' I,
	--"isCM:  " | net isCM quotient I,
	net ((j+1)*(flatten degrees ring I)),
	netList {
--	    minimalBetti (map(S', S', apply(gens S', g -> if degree g < {3} then 0 else g))) I,
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
