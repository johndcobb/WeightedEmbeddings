--this file is in the public domain

newPackage(
    "SectionRing",
    Date => "May 22, 2025",
    Version => "0.3",
    Headline => "the section ring of a Weil Divisor",
    Authors => {
	{ Name => "Andrew Bydlon",  Email => "thelongdivider@gmail.com", HomePage => "http://www.math.utah.edu/~bydlon/" },
	{ Name => "Mahrud Sayrafi", Email => "mahrud@umn.edu",           HomePage => "https://math.umn.edu/~mahrud" }
    },
    PackageExports => {
	"Varieties",
	"WeilDivisors",
	"SubalgebraBases",
    },
    Keywords => { "Commutative Algebra", "Projective Algebraic Geometry" },
    DebuggingMode => true,
)

export{
	"globallyGenerated",
	"isMRegular",
	"mRegularity",
	"mRegular" => "mRegularity",
	"sectionRing",
}

-----------------------------------------------------------------------
-- Binary search algorithm
-----------------------------------------------------------------------

-- TODO: move to Core, c.f. https://github.com/Macaulay2/M2/issues/3844
-- assume 'test' is a monotonic function, i.e. false for all i < n then true for i >= n
binarySearch = method()
-- return the first index of an element in L such that test(L#i) is true
binarySearch(List,        Function) := (L,          test) -> binarySearch(0, #L-1, i -> test(L#i))
-- shorthand for search in [0, n)
binarySearch(         ZZ, Function) := (      high, test) -> binarySearch(0, high-1, test)
-- shorthand for when a lower bound isn't known
binarySearch(Nothing, ZZ, Function) := (null, high, test) -> (
    dist := 1;
    while true do if test(high - dist)
    then (high, dist) = (high - dist, dist * 2)
    else break binarySearch(high - dist + 1, high, test));
-- shorthand for when an upper bound isn't known
binarySearch(ZZ, Nothing, Function) := (low, null, test) -> (
    dist := 1;
    while true do if test(low + dist)
    then break binarySearch(low, low + dist, test)
    else (low, dist) = (low + dist + 1, dist * 2))
-- standard binary search
binarySearch(ZZ, ZZ, Function) := (low, high, test) -> (
    -- TODO: are the first two lines standard?
    if     test(low)  then return low;
    --if not test(high) then return high + 1;
    while high - low > 1 do (
	mid := (high + low) // 2;
	if test(mid) then high = mid else low = mid);
    high)

-----------------------------------------------------------------------
-- Find m such that OO_X(mD) is a globally generated line bundle
-----------------------------------------------------------------------

globallyGenerated = method()
globallyGenerated Ideal := I -> globallyGenerated divisor I
-- TODO: add globally generated for arbitrary module
globallyGenerated WeilDivisor := D -> (
    -- compute the smallest positive number (using a binary search)
    -- such that OO_X(mD) is globally generated for an ample OO_X(D).
    binarySearch(0, , a -> 1 % baseLocus(a*D) == 0))

-----------------------------------------------------------------------
-- Find m such that |mD| gives a finite birational map
-----------------------------------------------------------------------

-- TODO: find the correct name for this
-- finiteDegree = method()
-- finiteDegree Ideal := I -> finiteDegree divisor I
-- finiteDegree WeilDivisor := D -> (
--     -- Note: D needs to be an **ample Cartier divisor**
--     -- in order to give a finite map we need
--     -- the codimension of the divisor to be 1
--     binarySearch(0, , a -> 0 < codim baseLocus(a*D)))

-----------------------------------------------------------------------
-- Castelnuovo-Mumford's m-regularity with respect to an ample bundle B
-----------------------------------------------------------------------

isMRegular = method()
isMRegular(CoherentSheaf, ZZ) := (F, m) -> (
    -- whether a sheaf F on X is m-regular relative to OO_X(1)
    -- TODO: use Tate resolutions
    all(1 .. dim variety F, i -> HH^i(F(m-i)) == 0)
)
isMRegular(CoherentSheaf, CoherentSheaf, ZZ) := (F, B, m) -> (
    -- whether a coherent sheaf F on a projective variety X is m-regular
    -- with respect to a globally generated ample line bundle B
    -- see Definition 1.8.4 in Positivity in Algebraic Geometry I
    n := dim variety F;
    G := F ** B ^** (m - n - 1);
    all(n, j -> HH^(n-j)(G **= B) == 0)
)

-----------------------------------------------------------------------

mRegularity = method()
mRegularity Ideal := I -> (
    -- compute m for which OO_X(D) is m-regular relative to OO_X(1),
    -- where D is the divisor corresponding to a codim 1 ideal I.
    mRegularity dual sheaf I
)
mRegularity CoherentSheaf := F -> (
    -- compute m for which a sheaf F in m-regular relative OO_X(1)
    V := variety F;
    mRegularity(F, OO_V(1))
)
mRegularity(CoherentSheaf, CoherentSheaf) := (F, B) -> (
    -- computes m for which a sheaf F is m-regular relative to B,
    -- in the sense of Castelnuovo-Mumford, using a binary search
    if isMRegular(F, B, 0)
    -- tests for a negative-regularity in the case that F is 0-regular relative to B
    then binarySearch(, 0, a -> isMRegular(F, B, a))
    -- tests for positive-regularity in the case that F is NOT 0-regular relative to B
    else binarySearch(1, , a -> isMRegular(F, B, a))
)

-----------------------------------------------------------------------
-- Ring of sections of an ample line bundle on a projective variety
-----------------------------------------------------------------------

-- two small utilities for working with vectors of scalars
-- TODO: there must be a better way to implement these
substituteScalarVector = (R, L) -> apply(L, z -> sub(z, R))
isScalarVector = L -> (R := ring(L#0); all(L, z -> z == 0 or degree z == degree 1_R))

-- Given an ideal $I$ as input, dualizes the ideal, and maps it back into the ring,
-- producing $\operatorname{Hom}_R(I,R) \cong J \subset R$.
-- This method is used to produce the global sections $H^0(mD)$,
-- where $D$ is an integral divisor defined by $I$.
dualToIdeal = method()
dualToIdeal Ideal := I -> embedAsIdeal(dual module I, IsGraded => true)

sectionRingBound = I -> (
    -- gives a bound for the top degree where new sections may be found
    -- in examples about 75% of the computation is finding this bound
    R := ring I;
    X := variety R;
    -- shortcut for curves: use arithmetic genus
    -- this assumes R is generically Gorenstein
    -- and I is ample Cartier divisor
    if dim X == 1 then return 2 * genus X + 1;
    -- To apply the regularity theorem of Mumford, the ample OO_X(D) needs to be globally generated.
    -- Thus if OO_X(D) is not globally generated, we consider F = OO_X(2D), ... , OO_X((l-1)D)
    -- (which correspond to J#1, J#2,...) and F being relatively G-m-regular,
    -- where G = OO_X(lD) is globally generated.
    l := globallyGenerated I; -- ~45% of the computation is here alone
    J := apply(l, j -> sheaf Hom(I^[j+1], R));
    bound := max apply(l, j -> 1 + j + l * mRegularity(J#j, J#(l-1)));
    bound = max(l, bound) + 1)

sectionRing = method(
    Options => {
	DegreeLimit => null,
	"ReduceDegrees" => false,
	}
    )
sectionRing WeilDivisor := o -> D -> sectionRing ideal D
sectionRing Ideal := o -> I -> (
    -- compute the ring of sections of a semi-ample divisor associated to I
    -- TODO: be clear that R needs to be a domain
    R := ring I;
    K := coefficientRing R;

    -- This produces a bound, where all generators are found in lower degrees than bound.
    bound := o.DegreeLimit ?? sectionRingBound I;

    -- The next block of code produces a polynomial ring S with generators in degrees 1,2,3,...,bound
    -- which will then be quotiented to produce the section ring.

    -- this is Hom(I, R) represented as another ideal J in R
    Z := dualToIdeal I;
    Shift := Z#1;
    -- TODO: make the lists 0-based
    J := {0, reflexify((Z#0))};
    FF := { 0, basis(Shift, J#1) };
    -- n_i is the rank of HH^0(OO_X(iD))
    n := { 0, numColumns FF#1 };
    -- Map_i is the map HH^0(OO_X(iD)) -> J^i
    Map := { 0, gens image FF#1 };

    Y := local Y;
    Vars := { toList(Y_{1,1}..Y_{1,n#1}) };
    DegreeList := toList(n#1 : {1});

    i := 2;
    while (i < bound) do(
	-- TODO: is this assuming R is a normal domain?
	J = J | { reflexivePower(i, J#1) };
	FF = FF | { basis(i * Shift, J#i) };
	n = n | { numColumns FF#i };
	Map = Map | { gens image FF#i };
	Vars = Vars | { toList(Y_{i,1}..Y_{i,n#i}) };
	DegreeList = DegreeList | toList(n#i : {i});
	i = i+1;
    );

    S := K[flatten Vars, Degrees => DegreeList];
    numVars := numgens S;
    myVars := apply(Vars, z -> apply(z, x -> value(x)));

    -- compute the relations on S which define the section ring SR.
    -- we do so by going degree by degree (starting at degree 2),
    -- and computing the kernels of the morphisms
    -- \oplus_{i=0,...,[j/2]} HH^0((j-i)D) \otimes HH^0(iD) --> H^0(jD),
    -- and multiplying the matrix representing the kernel with
    -- the corresponding vector of variables of S, Vect_{j-i} \otimes Vect_i.
    -- This gives relations, then inserted into RelIdeal.

	RelIdeal := ideal(0);
	Spar := S;
	Vect := {0};

	c:=1;
	while((c<bound) and (n#c>0)) do (
		Vect = Vect | {transpose matrix{myVars#(c-1)}};
		c=c+1;
	);

	j:=2;
	while ( (dim(Spar) >  dim(R)) or (isDomain(Spar) != true)) do (

	-- Relations are achieved by finding the kernels of the direct sums
	-- of tensor products of global sections.  However, some efficiency
	-- improvements can be achieve by considering a minimal number of such sums/tensors.
	-- To do this, I consider partitions of the given degree of interest and throw out
	-- any partitions which are either above the bound in which our generators are
	-- considered, or can be factored through another partition.
	-- For example, O_V(D)^{\otimes 3} -> O_V(2D)\otimes O_V(D) -> O_V(3D),
	-- so if bound>1, then the partition (1,1,1) of 3 is excluded.
	-- Throughout, a is an index for which partition is chosen,
	-- and b is an index for an element of a given partition.
	-- Additionally, MapTot is the total map of lower degree tensors into the degree
	-- in which relations are being considered, VectTot the corresponding vector of variables.

		Part := partitions(j);
		LengP := #(Part);
		a:=0;
		AdmPart := {};
		while (a<LengP) do(
			if((Part#a#0 < bound) and ((Part#a)#(#(Part#a)-1) + (Part#a)#(#(Part#a)-2) > min(bound,j)-1)) then (
				AdmPart = AdmPart | {(Part)#a};
			);
			a=a+1;
		);

		LengP = #(AdmPart);

		a=0;

		TotMapTemp := Map#(AdmPart#a#0);
		TotVectTemp := Vect#(AdmPart#a#0);
		b := 1;
		LengPa := #((AdmPart)#a);
		while (b<LengPa) do (
			TotMapTemp = TotMapTemp ** Map#(AdmPart#a#b);
			TotVectTemp = TotVectTemp ** Vect#(AdmPart#a#b);
			b = b+1;
		);

		MapTot := TotMapTemp;
		VectTot := TotVectTemp;

		a=1;
		while(a<LengP) do (
			TotMapTemp = Map#(AdmPart#a#0);
			TotVectTemp = Vect#(AdmPart#a#0);

			b=1;
			LengPa = #(AdmPart#a);
			while (b<LengPa) do (
				TotMapTemp = TotMapTemp ** Map#(AdmPart#a#b);
				TotVectTemp = TotVectTemp ** Vect#(AdmPart#a#b);
				b = b+1;
			);

			MapTot = MapTot | TotMapTemp;
			VectTot = VectTot || TotVectTemp;
			a = a+1;
		);

		KerT := generators ker(MapTot);

		NumCols := numColumns(KerT);
		e := 0;

		while (e < NumCols) do (
			L := flatten entries KerT_{e};
			if isScalarVector L then (
				L = substituteScalarVector(S,L);
				Rel := sub((entries (matrix{L}*VectTot))#0#0,S);
				RelIdeal = trim(RelIdeal + ideal(Rel));
				Spar = S/RelIdeal;
			);
			e=e+1;
		);
		j=j+1;
	);

    -- improve the presentation of the ring, both in terms of
    -- having a more standard list of generators A_1...A_N,
    -- and eliminating linear relations and redundant generators
    A := local A;
    BetterS := K[A_1..A_(numgens S), Degrees => DegreeList];
    BetterMap := map(BetterS, S, vars BetterS);
    BetterRelIdeal := BetterMap(sub(RelIdeal,S));
    minimalPresentation(BetterS/BetterRelIdeal)
)

--
degreesRing' = memoize((rk, degs) -> ZZ( monoid [ Variables => #degs, DegreeRank => rk, Degrees => degs ] ))
exponents Matrix := m -> apply(numcols m, c -> first exponents m_(0,c))
sections = (deg, I) -> I.cache.sections#deg ??= basis(deg, ideal I_0^deg : I^deg)

sectionRing CoherentSheaf      := o ->  L -> sectionRing(L, 1, o)
sectionRing(CoherentSheaf, ZZ) := o -> (L, p) -> (
    -- TODO: also check ampleness?
    -- if not instance(variety L, ProjectiveVariety)
    -- or rank L != 1 or not isLocallyFree L
    -- then error "expected an ample line bundle on a projective variety";
    sectionRing(embedAsIdeal module dual L, p, o))

sectionRing Ideal      := o ->  I -> sectionRing(I, 1, o)
sectionRing(Ideal, ZZ) := o -> (I, p) -> I.cache#(symbol sectionRing, p, o) ??= (
    R := ring I;
    K := coefficientRing R;
    if p <= 0 then error "expected a positive exponent";
    I.cache.sections ??= new MutableHashTable;
    --I.cache.subalgebra ??= null;

    -- about 70% of the computation is finding the bound
    bound := o.DegreeLimit ?? sectionRingBound I;
    if debugLevel > 0 then printerr("computing sections up to degree ", bound);

    L := map(R^1, R^0, 0);
    deg := p;
    degs := {};
    while deg <= bound do (
	-- we want remainder _as subalgebras_
	if debugLevel > 0 then printerr("computing sections in degree ", toString deg);
	B := basis(deg, degreesRing'_1 degs); -- 10% of the remainder
	N := gens image sections(deg, I); -- ~75% of the remainder
	M := trim image(N % sub(B, L)); -- ~10% of the remainder
	--M := trim image subduction(sagbi(L, Limit => deg), N);
	deg += p;
	if M != 0 then (
	    printerr net gens M;
	    degs |= degrees M;
	    L |= gens M);
	);
    if degreeLength R == 1 then degs = flatten degs;
    if debugLevel > 0 then printerr("found ", numcols L, " sections in degrees ", degs);
    if o#"ReduceDegrees" then degs = degs // gcd degs;

///
    L = module dual sheaf I
    I = embedAsIdeal dual L
    a = ideal I_0
    deg = 1
    m = gens image basis(deg, a^deg : I^deg)

    deg += 1
    B := basis(deg, degreesRing'(1, degrees source m)); -- 10% of the remainder
    N := gens image basis(deg, a^deg : I^deg); -- ~75% of the remainder
    M := trim image(N % sub(B, m)) -- ~10% of the remainder
    m |= gens M


    L = module dual sheaf I
    I = embedAsIdeal dual L
    a = ideal I_0
    deg = 2
    m = gens image basis(deg, a^deg : I^deg)

    deg += 2
    B := basis(deg, degreesRing'_1 degrees source m); -- 10% of the remainder
    N := gens image basis(deg, a^deg : I^deg); -- ~75% of the remainder
    M := trim image(N % sub(B, m)) -- ~10% of the remainder
    m |= gens M


    L = dual sheaf I
    L2 = module L^**2
    J = embedAsIdeal dual L2
    b = ideal J_0
    deg = 2
    -- this works if the input is from ellipticCurve, but not curve
    m = gens image basis(deg, b^deg : J^(deg // 2))

    deg += 2
    B := basis(deg, degreesRing'_1 degrees source m); -- 10% of the remainder
    N := gens image basis(deg, b^deg : J^(deg // 2)); -- ~75% of the remainder
    M := trim image(N % sub(B, m)) -- ~10% of the remainder
    m |= gens M
///;
    s := symbol s;
    T := K(monoid[ s_0 .. s_(#degs - 1), Degrees => degs ]);
    T / ker map(R, T, L) -- 10%
)

sections' = (X, deg, I) -> X.cache.sections#(deg, I) ??= basis(deg, ideal I_0^deg : I^deg)

sectionRing(ProjectiveVariety, List, List) := o -> (X, II, pp) -> (
    R := ring X;
    K := coefficientRing R;
    if any(pp, p -> p <= 0) then error "expected positive exponents";
    X.cache.sections ??= new MutableHashTable;

    bound := o.DegreeLimit ?? error "multisection ring requires a DegreeLimit";
    if debugLevel > 0 then printerr("computing sections up to degree ", bound);
    bound = {1,1};

    error 0;
    I := II#0;
    p := pp#0;

    L := map(R^1, R^0, 0);
    degs := degrees source L;
    for deg in {0,0} .. bound do (
	if deg == {0,0} then continue;
	-- we want remainder _as subalgebras_
	if debugLevel > 0 then printerr("computing sections in degree ", toString deg);
	B := basis(deg, degreesRing'_2 degs); -- 10% of the remainder
	N := gens image sections'(X, deg, II); -- ~75% of the remainder
	M := trim image(N % sub(B, L)); -- ~10% of the remainder
	if M != 0 then (
	    printerr net gens M;
	    degs |= degrees M;
	    L |= gens M);
	);
    if degreeLength R == 1 then degs = flatten degs;
    if debugLevel > 0 then printerr("found ", numcols L, " sections in degrees ", degs);

    ///
    L := map(R^1, R^0, 0);
    degs = {}

    deg = {1,0}
    B := basis(deg, degreesRing'_2 degs)
    N := gens image basis(sum deg, ideal(intersect II)_0^(sum deg) : intersect apply(II, deg, (I, d) -> I^d))
    M := trim image(N % sub(B, L))
    degs |= toList(numgens M : deg)
    L |= gens M
    
    ///;
    

    s := symbol s;
    T := K(monoid[ s_0 .. s_(#degs - 1), Degrees => degs ]);
    T / ker map(R, T, L) -- 10%
)

-----------------------------------------------------------------------

beginDocumentation();

doc ///
Node
  Key
    SectionRing
  Headline
    computing the section ring of a Weil Divisor
  Description
    Text
      This package provides algorithms for computing the ring of sections a semi-ample Weil divisor.
    Tree
      :Main algorithm
       > sectionRing
      :Positivity Computations
       > globallyGenerated
       > mRegularity
       > isMRegular
  SeeAlso
    "WeilDivisors :: WeilDivisors"

Node
  Key
    globallyGenerated
   (globallyGenerated, WeilDivisor)
   (globallyGenerated, Ideal)
  Headline
    find smallest integer a such that OO_X(mD) is globally generated
  Usage
    globallyGenerated(D)
  Inputs
    D:{WeilDivisor,Ideal}
  Outputs
    :Number
  Description
    Text
      This method uses a binary search to find the smallest integer $m$ with the property
      that $|mD|$ is a basepoint-free linear series. In this case, the corresponding line
      bundle is globally generated.

Node
  Key
    isMRegular
   (isMRegular, CoherentSheaf, ZZ)
   (isMRegular, CoherentSheaf, CoherentSheaf, ZZ)
  Headline
    whether F is m-regular in the sense of Castelnuovo-Mumford
  Usage
    isMRegular(F,m)
    isMRegular(F,B,m)
  Inputs
    F:CoherentSheaf
      over a projective variety $X$.
    B:CoherentSheaf
      which is a globally generated ample line bundle on $X$;
      if omitted, assumes $B = \mathcal{O}_X(1)$.
    m:ZZ
  Outputs
    :Boolean
      whether $\mathcal F$ is $m$-regular with respect to $B$ in the sense of Castelnuovo-Mumford
  Description
    Text
      This method tests whether
      $$ H^i(\mathcal F \otimes B^{\otimes(m-i)}) = 0 \quad \text{for every} \quad i > 0.$$
      As soon as a non-zero cohomology is found, the algorithm stops and returns false.
      If none is found, $\mathcal F$ is $m$-$B$-regular, and it returns true.
  References
    See Definition 1.8.4 of Lazarsfeld's Positivity in Algebraic Geometry I.
  Caveat
    In the case $B = \mathcal{O}_X(1)$, it may be faster to use @TO "BGG::BGG"@
    or @TO "TateOnProducts::TateOnProducts"@ to compute many cohomologies at once.

Node
  Key
    mRegularity
   (mRegularity, Ideal)
   (mRegularity, CoherentSheaf)
   (mRegularity, CoherentSheaf, CoherentSheaf)
  Headline
    compute the Castelnuovo-Mumford regularity of F with respect to G
  Usage
    mRegularity(F)
    mRegularity(F,G)
  Inputs
    F:{CoherentSheaf,Ideal}
      over a projective variety $X$;
      given an ideal, assumes $OO_X(D)$ where $D$ is divisor associated to $I$.
    B:CoherentSheaf
      which is a globally generated ample line bundle on $X$;
      if omitted, assumes $B = \mathcal{O}_X(1)$.
  Outputs
    :ZZ
  Description
    Text
      This method utilizes a binary search to compute the smallest $m$ such that $\mathcal F$
      is $m$-regular with respect to $B$, utilizing the function @TO "isMRegular"@.
      computes the regularity of O_X(D), where D is the associated divisor to I.

Node
  Key
    sectionRing
   (sectionRing, WeilDivisor)
   (sectionRing, Ideal)
  Headline
    compute the section ring of an ample divisor
  Usage
    sectionRing(D)
  Inputs
    D:{WeilDivisor,Ideal}
      an ample divisor on a projective variety $X$;
      given an ideal, the corresponding divisor is used.
  Outputs
    :Ring
  Description
    Text
      This algorithm begins by computing the regularity $m$ of
      $\mathcal O_X, \mathcal O_X(D), \mathcal O_X(2D), \dots, \mathcal O_X((l-1)D)$
      with respect to $\mathcal O_X(lD)$, where $l$ is the smallest integer for
      which $\mathcal O_X(lD)$ is globally generated.

      Mumford's Theorem (1.8.5 in Positivity in Algebraic Geometry I) implies that each of the maps
      $\mathcal O_X(iD) \otimes \mathcal O_X(lD)^{\otimes m} \to \mathcal O_X((i+ml)D)$ is surjective.
      Thus, all generators for the section ring can be assumed in lower degree than bound.
      Thus it forms a polynomial ring $S$ over the base field with $h^0(iD)$-many generators in degree $i$,
      for $i = 1,2,\dots,\mathrm{bound}-1$.

      Next, relations in degree $d$ are computed by considering the total maps
      $\oplus_{\mathrm{partitions } P \mathrm{ of } d} \otimes_{i\in P} \mathcal O_X(i D) \to \mathcal O_X(dD)$.
      Each of these relations is then quotiented, until the point that a domain of the correct dimension is produced.
      Some steps are then performed to make the output more readable and standard.
  SeeAlso
    globallyGenerated
///

-----------------------------------------------------------------------

TEST ///
R = QQ[x,y,z]/ideal(x^3+y^3-z^3);
I = ideal(x,y-z);
assert( globallyGenerated ideal R == 0)
assert( globallyGenerated(I) == 2)
///


TEST ///
R = QQ[x,y,z]/ideal(x^4+y^4-z^4);
I = ideal(x,y-z);
assert( globallyGenerated ideal R == 0)
assert( globallyGenerated(I) == 3)
///

TEST ///
R = QQ[x,y,z]/ideal(x^5+y^5-z^5);
I = ideal(x,y-z);
assert( globallyGenerated ideal R == 0)
assert( globallyGenerated(I) == 4)
///

TEST ///
X = Proj(QQ[x,y,z,w,f]);
F = OO_X(4);
G = OO_X(-2);
assert(not isMRegular(F, -5) and isMRegular(F, -4))
assert(not isMRegular(F, OO_X(1), -5) and isMRegular(F, OO_X(1), -4))
assert(mRegularity F == -4 and mRegularity G == 2)
///

TEST ///
R = QQ[x,y,z,w,f];
I = ideal(x-y+w);
S = sectionRing I;
assert( (#(vars S)) == dim S)
///

TEST ///
R = QQ[x,y,z]/(x^3+y^3-z^3)
I = ideal(x,y-z);
elapsedTime S = sectionRing I;
J = ideal S;
assert isHomogeneous S
assert(degrees S == {{1}, {2}, {3}})
assert(degrees J == {{6}})
assert(toString J == "ideal(s_1^6-s_2^3-3*s_1^3*s_3+3*s_3^2)")
///

TEST ///
  needsPackage "SpaceCurves"
  needsPackage "SectionRing"

  C = curve(5, 1)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  elapsedTime assert(degrees sectionRing(I, 1, DegreeLimit => 6) == {{1}, {2}, {3}})
  elapsedTime assert(degrees sectionRing(I, 2, DegreeLimit => 6) == {{2}, {2}, {4}})
  elapsedTime assert(degrees sectionRing(I, 3, DegreeLimit => 6) == {{3}, {3}, {3}})
  L = dual sheaf I;
  elapsedTime assert(degrees sectionRing(L, 1, DegreeLimit => 6) == {{1}, {2}, {3}})
  elapsedTime assert(degrees sectionRing(L, 2, DegreeLimit => 6) == {{2}, {2}, {4}})
  elapsedTime assert(degrees sectionRing(L, 3, DegreeLimit => 6) == {{3}, {3}, {3}})
  elapsedTime assert(degrees sectionRing(L, 4, DegreeLimit => 6) == {{4}, {4}, {4}, {4}})

  -- TODO: is this fixable?
  -- I2 = embedAsIdeal module dual L^**2
  -- isIsomorphic(L^**2, dual sheaf I2)
  -- degrees sectionRing(I2, 1, DegreeLimit => 6)
  -- degrees sectionRing(I2, 2, DegreeLimit => 6)

  C = curve(5, 2)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  elapsedTime assert(degrees sectionRing(I, 1, DegreeLimit => 8) == {{1}, {3}, {4}, {5}})
  elapsedTime assert(degrees sectionRing(I, 2, DegreeLimit => 8) == {{2}, {4}, {4}, {6}, {6}})
  elapsedTime assert(degrees sectionRing(I, 3, DegreeLimit => 8) == {{3}, {3}, {6}, {6}})
  elapsedTime assert(degrees sectionRing(I, 4, DegreeLimit => 8) == {{4}, {4}, {4}, {8}})
  elapsedTime assert(degrees sectionRing(I, 5, DegreeLimit => 8) == {{5}, {5}, {5}, {5}})
  elapsedTime assert(degrees sectionRing(I, 6, DegreeLimit => 8) == {{6}, {6}, {6}, {6}, {6}})

  C = curve(6, 3)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  elapsedTime assert(degrees sectionRing(I, 1, DegreeLimit => 10) == {{1}, {4}, {5}, {6}, {7}})
  elapsedTime assert(degrees sectionRing(I, 2, DegreeLimit => 10) == {{2}, {4}, {6}, {6}, {8}})
  elapsedTime assert(degrees sectionRing(I, 3, DegreeLimit => 10) == {{3}, {6}, {6}, {6}, {9}, {9}, {9}})
  elapsedTime assert(degrees sectionRing(I, 4, DegreeLimit => 10) == {{4}, {4}, {8}, {8}, {8}})
  elapsedTime assert(degrees sectionRing(I, 5, DegreeLimit => 10) == {{5}, {5}, {5}, {10}, {10}})
  elapsedTime assert(degrees sectionRing(I, 6, DegreeLimit => 10) == {{6}, {6}, {6}, {6}})
  elapsedTime assert(degrees sectionRing(I, 7, DegreeLimit => 10) == {{7}, {7}, {7}, {7}, {7}})
///

///
  restart
  needsPackage "SpaceCurves"
  needsPackage "SectionRing"
  C = curve(7, 5)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  scan(1 .. 9, l -> print degrees sectionRing(I, l, DegreeLimit => 16))

  ----
  C = curve(3, 1)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  scan(1 .. 10, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 10, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net minimalBetti J }))

  ----
  C = curve(5, 2)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  scan(1 .. 10, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 10, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net betti res J }))

  ----
  S = ZZ/11[x_0..x_3]
  C = curve(6, 3)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  scan(1 .. 10, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 10, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net minimalBetti J }))

  ----
  C = curve(7, 4)
  R = quotient ideal C;
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  -- 20s
  elapsedTime scan(1 .. 10, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 10, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net minimalBetti J }))

  M = canonicalBundle(Proj R, MinimalGenerators => false);
  M = dual dual M;
  sectionRing(M, 1, DegreeLimit => 10, "ReduceDegrees" => true) -- TODO: why so slow

  -- a nonhyperelliptic example for g=4 is an intersection of
  -- a quadric surface and a cubic surface in P^3
  S = kk[x_0..x_3]
  R = quotient ideal(random(2, S), random(3, S))
  while euler(I = first decompose ideal random(1, R)) != 1 do ()
  scan(1 .. 10, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 10, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net minimalBetti J }))

  restart
  needsPackage "SpaceCurves"
  needsPackage "SectionRing"
  S = ZZ/32003[x,y,z]
  -- a quartic passing simply through [1,0,0]
  R = quotient ideal random(5, ideal(y,z))
  while euler(I = first decompose ideal ideal(R_1,R_2)) != 1 do ()
  scan(1 .. 5, l -> print degrees sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true))

  apply(1 .. 5, l -> (
	  J := ideal sectionRing(I, l, DegreeLimit => 20, "ReduceDegrees" => true);
	  stack { net flatten degrees ring J, net minimalBetti J }))
///

///
  needsPackage "BundlesOnCurves"
  needsPackage "SectionRing"
  C = ellipticCurve 5
  I = preimage(C.cache.WeightedRingMap, C.cache.WeightedPoints#0)
  elapsedTime SectionRing$sectionRing(I, 1, DegreeLimit => 6)
  elapsedTime SectionRing$sectionRing(I, 2, DegreeLimit => 6)
  elapsedTime SectionRing$sectionRing(I, 3, DegreeLimit => 6)
  elapsedTime BundlesOnCurves$sectionRing(ring I, I)
///

///
  restart
  needsPackage "NormalToricVarieties"
  Z = (toricProjectiveSpace 1)^**2
  Y = (toricProjectiveSpace 3)
  f = map(ring Z, ring Y, monomials(Z_0 + Z_2))
  R = quotient ker f
  X = Proj R

  needsPackage "SectionRing"
  I = sub(preimage(f, ideal random({1, 1}, ring Z)), vars R)
  sectionRing(I, 1, DegreeLimit => 5)

  I1 = sub(preimage(f, ideal random({1, 0}, ring Z)), vars R)
  I2 = sub(preimage(f, ideal random({0, 1}, ring Z)), vars R)
  II = {I1, I2}
  pp = {1, 1}
  sectionRing(X, II, pp, DegreeLimit => 5)

  

  I = ideal random({1,1}, S)
  
  -- TODO: bigraded sectionRing!
  d = {1,1}
  m = basis(d, S)
  n = numcols m
  T = kk[y_0..y_(n-1)]
  phi = map(S, T, m)
  I = ker phi
  R = T/I
  X = Proj R
  assert(dim X == 2)
  assert(degree X == 9)
  hilbertPolynomial(X, Projective => false)
  assert(rank HH^0 OO_X^1 == 1)
  assert(genus(R/random(1, R)) == 1)
///

end

restart
needsPackage "SectionRing"
check "SectionRing"

installPackage "SectionRing"
viewHelp oo
