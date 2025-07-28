-* Jay says:

Here's some code for embedding hyperelliptics. I'm convinced that the embedding into P1xP1 can't be smooth in general, at least not without some weird change of coordinates.

There are three sections to the code, the first two are the two different cases of embedding into a Hirzebruch, the even and odd degree case, and then at the bottom there is the code to embed the Hirzerbruch into P^n, Hopefully this does what you need. If you want something that doesn't require writing the curve in by hand, or if there's something that doesn't work, let me know, I can put together some code to do the homogenization.

*-



--even degree case, d=6, Hirzebruch for d/2
restart
needsPackage "NormalToricVarieties"
X = hirzebruchSurface 3
S = ring X
vars S
B = ideal X
degrees S
--this is for y^2=x(x-1)(x-2)...(x-5), y~x_3, x~x_0, homogenizing variables are x_1 and x_2
I = ideal(x_3^2-x_1^2*x_0*(x_0-x_2)*(x_0-2*x_2)*(x_0-3*x_2)*(x_0-4*x_2)*(x_0-5*x_2)) 
isHomogeneous I
J = minors_1 jacobian I
--smooth on the actual geometry
saturate(radical trim (I+J),B)

--odd degree case, d=5, Hirzebruch for (d-1)/2
needsPackage "NormalToricVarieties"
X = hirzebruchSurface 2
S = ring X
vars S
B = ideal X
degrees S
--this is for y^2=x(x-1)(x-2)...(x-4), y~x_3, x~x_0, homogenizing variables are x_1 and x_2
I = ideal(x_2*x_3^2-x_1^2*x_0*(x_0-x_2)*(x_0-2*x_2)*(x_0-3*x_2)*(x_0-4*x_2)) 
isHomogeneous I
J = minors_1 jacobian I
--smooth on the actual geometry
saturate(radical trim (I+J),B)


--embed the Hirzebruch by the (1,1) divisor
b = basis({1,1},S);
Y = toricProjectiveSpace (numColumns b - 1)
R = ring Y
B = ideal Y
f = map(S,R,b)
assert(isWellDefined f)
--If I is the ideal for a subvariety of the hirzebruch, this gives the ideal for the embedding
--into the P^N
I' = preimage (f,I);
--check smoothness
J' = minors_2 jacobian I'
saturate(radical trim (I'+J'),B)
