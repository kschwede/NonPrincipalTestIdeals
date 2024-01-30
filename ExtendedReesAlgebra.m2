extendedReesAlgebra = method(Options => {});

extendedReesAlgebra(Ideal) := opts->(J1) -> (    
    I1 := reesIdeal(J1, Trim => true);
    degList := (apply(gens ring reesIdeal J, j -> 1)) | {-1};
    T2 := ring(J1)[(gens ring reesIdeal J)|{ti}, Degrees=>degList];
    --S2 := T2/(sub(I1, T2));    
    L1 := apply(gens ring I1, u -> sub(u, T2));
    L0 := apply(first entries mingens J1, h -> sub(h, T2));
    S2 := T2/((sub(I1, T2) + ideal( apply(#(gens ring I1), j -> ti*(L1#j) - (L0#j)))));
    S2
)






end 
restart
break
load "ExtendedReesAlgebra.m2"
 R = ZZ/3[x,y,z] --higher characteristics really get slow
 J = ideal(x^2, z*x, y^2, z^3);
 J = ideal(x^3,y^4,z^4,random(2, R));
 S = (flattenRing extendedReesAlgebra(J))#0
 T = (flattenRing reesAlgebra(J))#0
 ideal S
 ideal T
 minimalPrimes(ideal(0_S))
 minimalPrimes(ideal(0_T))

 loadPackage( "TestIdeals", Reload=>true, DebuggingMode=>true)
 debugLevel = 1
 time testModule S;
time testModule T;

R = ZZ/3[a..h];
M = matrix{{a,b,c,d},{e,f,g,h}};
J = minors(2,M)
S = (flattenRing extendedReesAlgebra(J))#0
 minimalPrimes(ideal(0_S))