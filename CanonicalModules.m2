

canonicalModule = method(Options=>{})
canonicalModule(Ring) := WeilDivisor => o->(R1) -> (
	S1 := ambient R1;
	I1 := ideal R1;
	dR := dim R1;
	dS := dim S1;
	varList := first entries vars S1;
	degList := {};
	if (#varList > 0) then ( --then there are no variables
        if (#(degree(varList#0)) == 1) then (
		    degList = apply(varList, q -> (degree(q))#0); )
	    else (
		    degList = apply(varList, q -> (degree(q))); );
	);
    print degList;
    print (-(sum degList));
	M1 := Ext^(dS - dR)(S1^1/I1, S1^{-(sum degList)})
)