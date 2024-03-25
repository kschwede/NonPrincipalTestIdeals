newPackage(
    "NonPrincipalTestIdeals",
    Version => "0.0",
    Date => "November 1, 2023",
    Authors => {{Name => "Rahul Ajit", Email => "", HomePage => ""},
        {Name => "Matthew Bertucci", Email => "", HomePage => ""}, 
        {Name => "Trung Chau", Email => "", HomePage => ""}, 
        {Name => "Karl Schwede", Email => "", HomePage => ""},
        {Name => "Hunter Simper", Email => "", HomePage => ""}},
    Headline => "",
    Keywords => {},
    DebuggingMode => true,
    Reload=>true, 
    PackageImports => {"ReesAlgebra"},
    PackageExports => {"TestIdeals", "FrobeniusThresholds"}
    )
export{
    "extendedReesAlgebra",
    "canonicalModule2",
    "reesModuleToIdeal",
    "gradedReesPiece",
    "testIdealNP",
    "isFJumpingExponentNP",
    --"IsGraded",
    "AmbientCanonical",--option
    "ExtendedReesAlgebra",--Type    
    --"ReturnMap",
    "Map",
}

--needsPackage "ReesAlgebra"
needsPackage "Divisor"
--needsPackage "TestIdeals"
--load "ExtendedReesAlgebra.m2"
--load "CanonicalModules.m2"

--the degress need to be fixed to work with extended Rees algebras
canonicalModule2 = method(Options=>{AmbientCanonical => null})
canonicalModule2(Ring) := Module => o->(R1) -> (
	S1 := ambient R1;
	I1 := ideal R1;
	dR := dim R1;
	dS := dim S1;
	varList := first entries vars S1;
	degList := {};
    degSum := 0;
    local ambcan;
    if o.AmbientCanonical === null then (
        if (R1#?"ExtendedReesAlgebra") and (R1#"ExtendedReesAlgebra") then (
            varList = select(varList, z -> ((degree z)#0 >= 0));
            degList = apply(varList, q -> (degree(q)));
            --print degList;
            degSum = -(sum degList)+{1,0};
        )
        else if (#varList > 0) then ( --then there are no variables
            if (#(degree(varList#0)) == 1) then (
                degList = apply(varList, q -> (degree(q))#0); )
            else (
                degList = apply(varList, q -> (degree(q))); );
            degSum = -(sum degList);
        );
--        print degList;
  --      print degSum;
        --print degList;
        --print (-(sum degList));
        ambcan = S1^{degSum}; -- these degrees are probably wrong for us, fix it.
    )
    else (
        ambcan = o.AmbientCanonical;
        --print (degrees ambcan);
    );
	M1 := (Ext^(dS - dR)(S1^1/I1, ambcan))**R1
)

ClassicalReesAlgebra = new Type of QuotientRing
ExtendedReesAlgebra = new Type of QuotientRing

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
    local degList;
    if isHomogeneous J1 then ( 
        degList = apply( (degrees ring J1), j->{0,sum j} ) | (degrees ring I1) | {{-1,0}};
    )
    else(
        degList = apply( (degrees ring J1), j->{0,0} ) | apply(degrees ring I1, j->{1,0}) | {{-1,0}};
    );
--    print degList;
    ti := getSymbol "ti";
    T2 := (coefficientRing ring(J1))[ (gens ring J1)|(gens ring I1)|{ti}, Degrees=>degList];
    ti = last gens T2;
    --T2 = ambient reesAlgebra J1; 
    --S2 := T2/(sub(I1, T2));    
    L1 := apply(gens ring I1, u -> sub(u, T2));
    reesList := first entries mingens J1;
    L0 := apply(reesList, h -> sub(h, T2));
    S2 := T2/((sub(ideal ring J1, T2) + sub(I1, T2) + ideal( apply(#(gens ring I1), j -> ti*(L1#j) - (L0#j)))));
    S2#"InverseVariable" = sub(ti, S2);
    S2#"BaseRing" = ring J1;
    S2#"Degree1" = apply(gens ring(I1), z -> sub(z, S2));
    S2#"OriginalList" = apply(L0, z->sub(z, S2));
    S2#"BaseRingList" = reesList;
    S2#"ExtendedReesAlgebra" = true;    
    S2
)

classicalReesAlgebra = method(Options => {});

classicalReesAlgebra(Ideal) := opts -> (J1) -> (
    if any (degrees ring J1, ll -> #ll > 1) then error "classicalReesAlgebra: currently only works for singly graded ambient rings";
--    I1 := reesIdeal(J1, Variable=>getValidVarName(ring J1));
    Rees2 := reesAlgebra J1;
--    degList := apply( (degrees ring J1), j->{0,sum j} ) | (degrees ring I1);
--    print degList;
--    T2 := (coefficientRing ring(J1))[ (gens ring J1)|(gens ring I1), Degrees=>degList];
    --ti = last gens T2;
    --T2 = ambient reesAlgebra J1; 
    --S2 := T2/(sub(I1, T2));    
    reesList := first entries mingens J1;
    S2 := (flattenRing Rees2)#0;--:= T2/((sub(ideal ring J1, T2) + sub(I1, T2) + ideal( apply(#(gens ring I1), j -> ti*(L1#j) - (L0#j)))));
    S2#"BaseRing" = ring J1;
    S2#"Degree1" = apply(gens Rees2, z -> sub(z, S2));
    S2#"OriginalList" = apply(reesList, z->sub(z, S2));
    S2#"BaseRingList" = reesList;
    S2#"ClassicalReesAlgebra" = true;    
    S2
);


--this should be like basis(n, M)
gradedReesPiece = method(Options => {});

gradedReesPiece(ZZ, Ideal) := opts -> (n1, J1) -> (
    S1 := ring J1;
    if not ((S1#?"ExtendedReesAlgebra") or (S1#?"ClassicalReesAlgebra")) then error "gradedReesPiece:  Expected a ClassicalReesAlgebra or ExtendedReesAlgebra"; 
    R1 := S1#"BaseRing";
    genList := first entries gens J1;
    degList := apply(genList, zz->first (degree zz) );
    baseGens := S1#"BaseRingList";
    tempGens := ideal(0_R1);
    local badMap;
    local i;
    if (S1#?"ExtendedReesAlgebra") and (S1#"ExtendedReesAlgebra" == true) then (
        --if not isHomogeneous J1 then error "gradedReesPiece:  Expected a homogeneous ideal or a Reese pieces";
        --something is not working right, we should remove this error, and then debug
        badMap = map(R1, S1, (gens R1) | baseGens | {1}); --this is not well defined, but it should do the job.
        i = 0;
        while (i < #genList) do (
            if (degList#i == n1) then (
                tempGens = tempGens + ideal(badMap(genList#i));
            )
            else if (degList#i > n1) then (
                tempGens = tempGens + badMap(((S1#"InverseVariable")^((degList#i) - n1))*ideal((genList#i)));
            )
            else if (degList#i < n1) then (
                tempGens = tempGens + (ideal(badMap(genList#i)))*(ideal baseGens)^(n1 - degList#i);
            );
            i = i+1;
        );
        return tempGens;
    )
    else if (S1#?"ClassicalReesAlgebra") and (S1#"ClassicalReesAlgebra" == true) then (
        if not isHomogeneous J1 then error "gradedReesPiece:  Expected a homogeneous ideal or a Reese pieces";
        badMap = map(R1, S1,  baseGens | (gens R1) ); --this is not well defined, but it should do the job.
        i = 0;
        while (i < #genList) do (
            if (degList#i == n1) then (
                tempGens = tempGens + ideal(badMap(genList#i));
            )
            else if (degList#i < n1) then (
                tempGens = tempGens + (ideal(badMap(genList#i)))*(ideal baseGens)^(n1 - degList#i);
            );
            i = i+1;
        );
        return tempGens;
    )
    else (
        error "gradedReesPiece: expected a module over a ClassicalReesAlgebra or ExtendedReesAlgebra.";
    )
);


--currently not working in this multi-graded setting
reesModuleToIdeal = method(Options => {MTries=>10, Homogeneous=>false, Map=>false});

reesModuleToIdeal(Ring, Module) := Ideal => o ->(R1, M2) -> 
(--turns a module to an ideal of a ring
--	S1 := ambient R1;
	flag := false;
	answer:=0;
	if (M2 == 0) then ( --don't work for the zero module	    
	    answer = ideal(sub(0, R1));
	    if (o.Homogeneous==true) then (		    
			answer = {answer, degree (sub(1,R1))};
		);
		if (o.ReturnMap==true) then (
		    if (#entries gens M2 == 0) then (
		        answer = flatten {answer, map(R1^1, M2, sub(matrix{{}}, R1))};
		    )
		    else (
			    answer = flatten {answer, map(R1^1, M2, {apply(#(first entries gens M2), st -> sub(0, R1))})};
			);
		);

	    return answer;
	);
--	M2 := prune M1;
--	myMatrix := substitute(relations M2, S1);
--	s1:=syz transpose substitute(myMatrix,R1);
--	s2:=entries transpose s1;
	s2 := entries transpose syz transpose presentation M2;
	h := null;
	--first try going down the list
	i := 0;
	t := 0;
	d1 := 0;
	while ((i < #s2) and (flag == false)) do (
		t = s2#i;
		h = map(R1^1, M2**R1, {t});
		if (isWellDefined(h) == false) then error "internalModuleToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(t);
			if (o.Homogeneous==true) then (
				--print {degree(t#0), (degrees M2)#0};
				d1 = degree(t#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.Map==true) then (
				answer = flatten {answer, h};
			)
		)
        else (print "warning");
		i = i+1;
	);
	-- if that doesn't work, then try a random combination/embedding
     i = 0;
	while ((flag == false) and (i < o.MTries) ) do (
		coeffRing := coefficientRing(R1);
        print coeffRing;
		d := sum(#s2, z -> random(coeffRing, Height=>100000)*(s2#z));
       -- print d;
		h = map(R1^1, M2**R1, {d});
		if (isWellDefined(h) == false) then error "internalModuleToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(d);
			if (o.Homogeneous==true) then (
				d1 = degree(d#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.Map==true) then (
				answer = flatten {answer, h};
			)
		);
        i = i + 1;
	);
	if (flag == false) then error "internalModuleToIdeal: No way found to embed the module into the ring as an ideal, are you sure it can be embedded as an ideal?";
	answer
);


testIdealNP = method(Options =>{});
testIdealNP(QQ, Ideal) := opts -> (n1, I1) -> (
    R1 := ring I1;
    p1 := char R1;
    local omegaS1;
    local omegaS1List;
    local tauOmegaSList;
    local tauOmegaS;
    local degShift;
    local S1;
    local answer;
    if (floor n1 == n1-2) then (
        --I turned this off for now.  
        --integer, can use ordinary Rees algebras.  Need to implement that.
        --S1 = (flattenRing(reesAlgebra(I1)))#0;
        --S1#"BaseRing" = R1;
        --S1#"Degree1" = apply(gens ring(reesIdeal I1), z -> sub(z, S1));
        --reesList := first entries mingens I1;
--        L0 := apply(reesList, h -> sub(h, T2));
        --S1#"OriginalList" = apply(reesList, z->sub(z, S1));
        --S1#"BaseRingList" = reesList;
        --S1#"ReesAlgebra" = true;
        S1 = classicalReesAlgebra(I1);  
        omegaS1 = canonicalModule2(S1);
        omegaS1List = reesModuleToIdeal(S1, omegaS1, Homogeneous=>true, Map => true);
        tauOmegaSList = testModule(S1, AssumeDomain=>true, CanonicalIdeal=>omegaS1List#0);
        degShift = (omegaS1List#1)#0;
        answer = gradedReesPiece(degShift + floor n1, tauOmegaSList#0);
    )
    else ( --we do the extended Rees algebra thing
        S1 = extendedReesAlgebra(I1);
        tvar := S1#"InverseVariable";
        omegaS1 = prune canonicalModule2(S1);  
        --print omegaS1;      
        omegaS1List = reesModuleToIdeal(S1, omegaS1, Homogeneous=>true, Map => true);
        --degShift = (omegaS1List#1)#0;
        --answer = gradedReesPiece(degShift, omegaS1List#0);
        --1/0;
        tauOmegaSList = testModule(n1, tvar, AssumeDomain=>true, CanonicalIdeal=>omegaS1List#0);
        tauOmegaS = tauOmegaSList#0;
        --print tauOmegaS;
        degShift = (omegaS1List#1)#0;
        --print degShift;
        answer = gradedReesPiece(degShift, tauOmegaS);
    );
    trim answer
);

testIdealNP(ZZ, Ideal) := opts -> (n1, I1) -> (
    testIdealNP(n1/1, I1, opts) 
);

isFJumpingExponentNP = method(Options =>{});

isFJumpingExponentNP(QQ, Ideal) := opts -> (n1, I1) -> (
    R1 := ring I1;
    pp := char R1;
    local computedHSLGInitial;
    local computedHSLG;
    local tauOmegaSList;
    local answer1;
    local answer2;    
    local tauOmegaS;
    S1 := extendedReesAlgebra(I1);
    --print "testing";
    tvar := S1#"InverseVariable";
    omegaS1 := canonicalModule2(S1);
    --print "test1";
    omegaS1List := reesModuleToIdeal(S1, omegaS1, Homogeneous=>true, Map => true);
    degShift := (omegaS1List#1)#0;
    if not (gradedReesPiece(degShift, omegaS1List#0) == ideal(sub(1, R1))) then error "isFJumpingExponent (non-principal case): not yet implemented for non(-obviously-)quasi-Gorenstein rings";--in the future, do some more work in this case to handle the Q-Gorenstein setting.   
    --print "test2";
    baseTauList := testModule(S1, AssumeDomain=>true, CanonicalIdeal=>omegaS1List#0);
    --print "test3";
    baseTau := baseTauList#0;
    genList := baseTauList#2;

    --now we have to run the sigma computation
    ( a1, b1, c1 ) := decomposeFraction( pp, n1, NoZeroC => true );
    if (instance(genList, RingElement)) then (
        tauOmegaSList = testModule(n1, tvar, AssumeDomain=>true, GeneratorList => {genList}, CanonicalIdeal => omegaS1List#0);
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { tvar }, CanonicalIdeal => baseTau, GeneratorList => { genList } );
        --print "test4";
        computedHSLG = frobeniusRoot(b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), genList, sub(computedHSLGInitial, ambient S1));
        --print "test5";
        tauOmegaS = tauOmegaSList#0;        
        answer1 = gradedReesPiece(degShift, tauOmegaS);
        answer2 = gradedReesPiece(degShift, computedHSLG*S1);
        return not(answer1 == answer2);
    )
    else if instance(genList, BasicList) then ( -- Karl: I haven't tested this
        tauOmegaSList = testModule(n1, tvar, AssumeDomain=>true, GeneratorList => genList, CanonicalIdeal => omegaS1List#0);
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { tvar }, CanonicalIdeal => baseTau, GeneratorList => genList );
        --print "test4";
        computedHSLG = frobeniusRoot(b1, apply(#genList, zz -> ceiling( ( pp^b1 - 1 )/( pp - 1 ) )), genList, sub(computedHSLGInitial, ambient S1));
        --print "test5";
        tauOmegaS = tauOmegaSList#0;        
        answer1 = gradedReesPiece(degShift, tauOmegaS);
        answer2 = gradedReesPiece(degShift, computedHSLG*S1);
        return not(answer1 == answer2);
    );
    error "isFJumpingExponent (non-principal case): something went wrong with the generator list for the Fedder colon";
);

isFJumpingExponent(ZZ, Ideal) := opts -> (n1, I1) -> (
    isFJumpingExponent(n1/1, I1)
);

--isFPT = method(Options)

isFPT(QQ, Ideal) := opts -> (n1, I1) -> (
     R1 := ring I1;
    pp := char R1;
    local computedHSLGInitial;
    local computedHSLG;
    local tauOmegaSList;
    local answer1;
    local answer2;    
    local tauOmegaS;
    S1 := extendedReesAlgebra(I1);
    --print "testing";
    tvar := S1#"InverseVariable";
    omegaS1 := canonicalModule2(S1);
    --print "test1";
    omegaS1List := reesModuleToIdeal(S1, omegaS1, Homogeneous=>true, Map => true);
    degShift := (omegaS1List#1)#0;
    targetAnswer := gradedReesPiece(degShift, omegaS1List#0);
    if not (targetAnswer == ideal(sub(1, R1))) then error "isFPT (non-principal case): not yet implemented for non(-obviously-)quasi-Gorenstein rings";--in the future, do some more work in this case to handle the Q-Gorenstein setting.   
    --print "test2";
    baseTauList := testModule(S1, AssumeDomain=>true, CanonicalIdeal=>omegaS1List#0);
    --print "test3";
    baseTau := baseTauList#0;
    genList := baseTauList#2;

    --now we have to run the sigma computation
    ( a1, b1, c1 ) := decomposeFraction( pp, n1, NoZeroC => true );
    if (instance(genList, RingElement)) then (
        tauOmegaSList = testModule(n1, tvar, AssumeDomain=>true, GeneratorList => {genList}, CanonicalIdeal => omegaS1List#0);
        tauOmegaS = tauOmegaSList#0;        
        answer1 = gradedReesPiece(degShift, tauOmegaS);
        if (targetAnswer == answer1) then return false; --we didn't hit the FPT
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { tvar }, CanonicalIdeal => baseTau, GeneratorList => { genList } );
        --print "test4";
        computedHSLG = frobeniusRoot(b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), genList, sub(computedHSLGInitial, ambient S1));
        --print "test5";
        answer2 = gradedReesPiece(degShift, computedHSLG*S1);
        if not (targetAnswer == answer2) then return false; --we went past the fpt
        return true;
    )
    else if instance(genList, BasicList) then ( -- Karl: I haven't tested this
        tauOmegaSList = testModule(n1, tvar, AssumeDomain=>true, GeneratorList => genList, CanonicalIdeal => omegaS1List#0);
        tauOmegaS = tauOmegaSList#0;        
        answer1 = gradedReesPiece(degShift, tauOmegaS);
        if (targetAnswer == answer1) then return false; --we didn't hit the FPT
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { tvar }, CanonicalIdeal => baseTau, GeneratorList => genList );
        --print "test4";
        computedHSLG = frobeniusRoot(b1, apply(#genList, zz -> ceiling( ( pp^b1 - 1 )/( pp - 1 ) )), genList, sub(computedHSLGInitial, ambient S1));
        --print "test5";        
        answer2 = gradedReesPiece(degShift, computedHSLG*S1);
        if not (targetAnswer == answer2) then return false; --we went past the fpt
        return not(answer1 == answer2);
    );
    error "isFPT (non-principal case): something went wrong with the generator list for the Fedder colon";
);


end--

