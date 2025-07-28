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

createHyperelliptic = method()
createHyperelliptic(ZZ) := Ideal => g -> (
    degR := 2*g+2;
    F := hirzebruchSurface(g+1);
    S := ring F;
    B := ideal F;

    -- Now the equation of a hyperelliptic curve can be written as y^2 = p(x), where p is a degree degR polynomial with 2g+2 roots (those are the branch points).
    p := product(for i from 1 to degR list (S_0-random(1,20)*S_2)); -- this is a degR polynomial at 8 branch points x=1...8 , in the O_(P^1) factor;

    C := ideal(S_3^2 - S_1^2*p);

    --embed the Hirzebruch by the (1,1) divisor
    b := basis({1,1},S);
    Y := toricProjectiveSpace (numColumns b - 1);
    R := ring Y;
    B := ideal Y;
    f := map(S,R,b);
    assert(isWellDefined f);
    --If I is the ideal for a subvariety of the hirzebruch, this gives the ideal for the embedding
    --into the P^N
    C' := preimage (f,C);
    C'
)