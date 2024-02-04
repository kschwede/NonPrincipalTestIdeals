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




end--