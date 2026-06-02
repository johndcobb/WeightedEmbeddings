needsPackage "WeightedEmbeddings"
topLevelMode = Standard

-- From Brown--Erman (Linear Syzygies of Curves in Weighted Projective Space)
g = 3
d = g -- g+3
A = ZZ/32003[z_2,z_1,z_0, Degrees => {g+1,1,1}]
f = z_2^2 - z_0^(2*g+2)-z_1^(2*g+2) - 5*z_0^(g+1)*z_1^(g+1)
A' = A/f

C = Proj A'
L = OO_C^{1}
apply(toList(1 .. 2*g), i -> (
	R := sectionRing(L, i, DegreeLimit => 30, "ReduceDegrees" => true);
	stack { net runLengthEncode flatten degrees R, net betti res ideal R }))

S = ZZ/101[x_0..x_4, Degrees => {1,1,1,2,2}]
phi = map(A', S, {z_1^2, z_1*z_0, z_0^2, z_2*z_1, z_2*z_0})
betti res ker phi

--So Proj(A') is a genus 2 curve realized as a hypersurface of degree
--6 in PP(1,1,3).
tex f

--Our base point D is [1:0:1].  We can check that it lies on the curve:
use A
sub(f,{z_0=>1, z_1 => 0 , z_2=> 1})
use A'


--Now we are going to embed with degree 5 and 10 sections from PP(1,1,3).
--So L will be the pullback of O(5) and L^2 will be the pullback of O(10).
--The pullback of L to the curve will have degree 10.
--You can see this by comparing with the hyperellptic map to P^1 (given by z_0,z_1)
--as z_0 and z_1 pullback to sections of that line bundle of degree 2.
--
--Now let's compute W_1, which is section of L that vanish on the point [1:0:1].
K = gens ker sub(basis(d, A'), {z_0=>1, z_1 => 0 , z_2=> 1})
--the point [1:0:1] is on the curve.
L1 = flatten entries(basis(d, A')*K)
#L1 == 2*(g+3) - g
L1
--L1 is W_1.
--Let's check that it has the right cardinality.
--L has degree 10 so by Riemann-Roch computation we should have
--dim H^0(L) = deg L + 1 - g = 10 + 1 - 2 = 9.
--but we want the sections that vanish at a point, so we should have 8 sections.
#L1 == 8
--Now let's compute W_2.  This will be called L2.
--Let's first confirm that L2 should have only two elements.
K1 = sort unique flatten apply(L1,i-> apply(L1,j-> i*j))
I1 = image matrix{K1};


--this is the image of Sym_2(W_1).
isHomogeneous I1
hilbertFunction(2*d,I1) == 4*(g+3) + 1 -g - 2
--the -2 is because it vanishes w/ mult 2 at [1:0:1]
--so this should be codim 2 in hilbertFunction(2*d,A')
--I.e. W_2 should have two elements.
--It's not hard to find two such elements:
L2 = {z_0^(2*d-1)*z_1,z_0^(2*d)}
--THese are independent module Sym_2(W_1)
matrix {L2} % ideal I1
--Now we are set to compute the Betti table.
L = L1|L2
S = ZZ/101[x_0..x_(#L1-1),y_0..y_(#L2-1),Degrees => apply(L1,i-> 1)| apply(L2,i-> 2)] 
phi = map(A',S,L);
I = ker phi;
betti res I
