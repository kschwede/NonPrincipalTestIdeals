getValidVarName = method();
getValidVarName(Ring) := (R1) -> (
    --this should be smarter, not sure the right way to do it.  This ought to work for now.
    s1 := toList("abcdefghijklmnopqrstuvwxyz");
    s1#(random (#s1))
)

extendedReesAlgebra = method(Options => {});

extendedReesAlgebra(Ideal) := opts->(J1) -> (    
    if any (degrees ring J1, ll -> #ll > 1) then error "extendedReesAlgebra: currently only works for singly graded ambient rings";
    I1 := reesIdeal(J1, Variable=>getValidVarName(ring J1));
    degList := apply( (degrees ring J1), j->{0,sum j} ) | (degrees ring I1) | {{-1,0}};
--    print degList;
    ti := getSymbol "ti";
    T2 := (coefficientRing ring(J1))[ (gens ring J1)|(gens ring I1)|{ti}, Degrees=>degList];
    ti = last gens T2;
    --T2 = ambient reesAlgebra J1; 
    --S2 := T2/(sub(I1, T2));    
    L1 := apply(gens ring I1, u -> sub(u, T2));
    L0 := apply(first entries mingens J1, h -> sub(h, T2));
    S2 := T2/((sub(ideal ring J1, T2) + sub(I1, T2) + ideal( apply(#(gens ring I1), j -> ti*(L1#j) - (L0#j)))));
    S2#inverse = sub(ti, S2);
    S2#reesIdeal = apply(gens ring(I1), z -> sub(z, S2));
    S2
)

end
restart
break
load "ExtendedReesAlgebra.m2"
R = ZZ/2[x,y]
R = ZZ/2[x,y, Degrees=>{0,0}]
m = ideal(x^3,y^3)
S = (flattenRing extendedReesAlgebra(m))#0
describe S

 loadPackage( "TestIdeals", Reload=>true, DebuggingMode=>true)
viewHelp testModule
testModule(S)
testModule(2/3, ti)


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