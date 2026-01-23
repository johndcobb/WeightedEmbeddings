debug needsPackage "DirectSummands"
needsPackage "SectionRing"
needs "WeightedEmbeddings.m2"
needs "../threads.m2"
allowableThreads = 32
notify = true

g = 2
kk = ZZ/101
--I0 = createHyperelliptic(kk, g)
R = kk[x_0..x_6]/{x_4*x_5-x_3*x_6,x_3*x_4-x_2*x_6,x_2*x_4-x_1*x_6,x_1*x_4-x_0*x_6,x_3^2-x_2*x_5,x_2*x_3-x_1*x_5,x_1*x_3-x_0*x_5,x_2^2-x_0*x_5,x_1*x_2-x_0*x_3,x_0*x_2+x_1*x_5-x_6^2,x_1^2+x_1*x_5-x_6^2,x_0*x_1+x_0*x_5-x_4*x_6,x_0^2+x_0*x_3-x_4^2}
assert(g == genus R)

randp = ideal {x_6,x_5,x_3,x_2,x_1,x_0+x_4}
assert(euler randp == 1)
-- S = kk[s_0..s_4, Degrees => {{1}, {2}, {2}, {3}, {3}}]
-- J = ideal {s_0^2*s_1-5*s_1^2+s_0*s_4,s_0*s_2^2-5*s_0^2*s_3-s_1*s_3,s_0*s_1^2-3*s_2*s_3+3*s_1*s_4,s_2^3-3*s_0*s_2*s_3-3*s_0*s_1*s_4+2*s_4^2,s_1*s_2^2-3*s_0*s_1*s_3+2*s_3*s_4,s_1^2*s_2+2*s_3^2,s_1^3-5*s_0*s_2*s_3-4*s_0*s_1*s_4,s_2^2*s_3-3*s_0*s_3^2-s_1*s_2*s_4,s_0^2*s_2*s_3-5*s_1*s_2*s_3-2*s_1^2*s_4-3*s_0*s_4^2,s_0^2*s_3^2-5*s_1*s_3^2+5*s_0*s_1*s_2*s_4}
J = ideal sectionRing(randp, 3, "ReduceDegrees" => true, DegreeLimit => 10)
S = ring J
minimalBetti J
--        0 1 2 3
-- total: 1 6 8 3
--     0: 1 . . .
--     1: . . . .
--     2: . . . .
--     3: . 1 . .
--     4: . 2 . .
--     5: . 3 2 .
--     6: . . 4 .
--     7: . . 2 1
--     8: . . . 2

-- evaluation map
use R
X = Proj quotient J
L = OO_X^{1}
W = directSum apply(degrees S, deg -> L^**(-deg#0));
ev = vars ring X -- randp.cache#("SectionMap", 2)
M = sheaf kernel ev

-- isIndecomposable M
-- # summands extendGroundField(5, M)
-- gensEnd0 (prune M).module

-- kernel bundle summands
-- debugLevel=1
-- errorDepth=2
-- ML = elapsedTime summands M

end--
restart
needs "genus-2-kernel-bundle-summands.m2"

m = matrix table(10, 10, (p,q) -> rank HH^1(exteriorPower(p+1, W) ** L^**(p+q)))
table(10, 10, (p,q) -> if m_(p,q) == 0 then exteriorPower(p+1, M) ** L^**(p+q));
matrix await table(10, 10, async((p,q) -> if m_(p,q) == 0 then rank HH^0(exteriorPower(p+1, M) ** L^**(p+q)) else -1))
