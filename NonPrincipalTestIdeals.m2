newPackage(
    "NonPrincipalTestIdeals",
    Version => "0.0",
    Date => "November 1, 2023",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "",
    Keywords => {},
    DebuggingMode => true,
    Reload=>true
    )
export{
    "extededReesAlgebra",
    "canonicalModule",
    "AmbientCanonical"--option
}

needsPackage "ReesAlgebra"
needsPackage "Divisor"
needsPackage "TestIdeals"
load "ExtendedReesAlgebra.m2"
--load "CanonicalModules.m2"
canonicalModule = method(Options=>{AmbientCanonical => null})
canonicalModule(Ring) := WeilDivisor => o->(R1) -> (
	S1 := ambient R1;
	I1 := ideal R1;
	dR := dim R1;
	dS := dim S1;
	varList := first entries vars S1;
	degList := {};
    local ambcan;
    if o.AmbientCanonical === null then (
        if (#varList > 0) then ( --then there are no variables
            if (#(degree(varList#0)) == 1) then (
                degList = apply(varList, q -> (degree(q))#0); )
            else (
                degList = apply(varList, q -> (degree(q))); );
        );
        --print degList;
        --print (-(sum degList));
        ambcan = S1^{-(sum degList)};
    )
    else (
        ambcan = o.AmbientCanonical;
        --print (degrees ambcan);
    );
	M1 := Ext^(dS - dR)(S1^1/I1, ambcan)
)

ClassicalReesAlgebra = new Type of Ring
ExtendedReesAlgebra = new Type of Ring

getValidVarName = method();
getValidVarName(Ring) := (R1) -> (
    --this should be smarter, not sure the right way to do it.  This ougt to work for now.
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
    S2#"inverseVariable" = sub(ti, S2);
    S2#"degree1" = apply(gens ring(I1), z -> sub(z, S2));
    S2#"originalList" = apply(L0, z->sub(z, S2));
    S2
)



--this should be like basis(n, M)
gradedReesPiece = method(Options => {});

gradedReesPiece(ZZ, Module) := opts -> (n1, M1) -> (
    if instance(ring M1, ClassicalReesAlgebra) then (

    )
    else if instance(ring M1, ExtededReesAlgebra) then (

    )
    else (
        error "gradedReesPiece: expected a module over a ClassicalReesAlgebra or ExtendedReesAlgebra.";
    )
);


end--