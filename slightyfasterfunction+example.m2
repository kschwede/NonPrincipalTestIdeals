
restart

--Here is a function automating the process from the proof of concept file
--slightly more optimized


------------------
needsPackage"BGG"
needsPackage"ReesAlgebra"
needsPackage"TestIdeals"
needsPackage"Divisor"

-------------------------------

---Note: right now may not work for t with denominator other than p (due to first bound computation)...should be easy fix

tIdeal = (I,t,e0,f0)->( ---I an ideal, t=a/p, and  e0, f0 natural numbers saying how long to run 
    p:=char ring I;
    RI:=reesAlgebra I;
    tau:=sub((testModule(first flattenRing RI))#0,RI);
    G:=divisor(sub(I,RI));
    e1:=1;
    lBound:=frobeniusRoot(1,{ceiling(t*(p))},{I});
    lBound1:={};
    for i from 1 to e0 do(
	e1=i;
	lBound1=lBound;
	lBound=frobeniusRoot(i+1,{ceiling(t*((p)^(i+1)))},{I});
	if lBound1==lBound then break;
	);
    f1:=0;
    uBound:={};
    for j from 1 to f0 do(
	f1=j;
	uBound=frobeniusRoot(j,embedAsIdeal(prune HH_0(directImageComplex (tau*ideal(p^j*t*G)*RI^1))));
    	if lBound==uBound then break;
	);
    return (uBound,e1,f1) 
    );

-------------------- can test with monomial ideals
needsPackage"MultiplierIdeals"


p=3;t=7/3;
S=ZZ[x,y,z];
J=ideal(x^2,x*z,y^2);

----
R0=QQ[flatten entries vars S];
J0=sub(J,R0);
-----
Rp=ZZ/p[flatten entries vars S] ;
Jp=sub(J,Rp);
------
timing(tIdeal(Jp,t,5,5))----this is kind of slow
multiplierIdeal( monomialIdeal J0,t)

-------
