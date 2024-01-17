extendedReesAlgebra = method(Options => {});

extendedReesAlgebra(Ideal) := opts->(J1) -> (
    S1 := reesAlgebra(J1);
    L1 := gens S1;
    L0 := apply(first entries mingens J1, h -> sub(h, S1));
    S2 := S1[ti]/ideal( apply(#(gens S1), j -> ti*(L1#j) - (L0#j)));
    S2
)






end 

load "ExtendedReesAlgebra.m2"
 R = QQ[x,y,z]
 J = ideal(x^5, y^4*z^3*x^3, y^5, y^3*z^3, z^4)
 J = ideal(x^3,y^4,z^4,random(2, R));
 S = (flattenRing extendedReesAlgebra(J))#0
 T = (flattenRing reesAlgebra(J))#0
 minimalPrimes(ideal(0_S))
 minimalPrimes(ideal(0_T))