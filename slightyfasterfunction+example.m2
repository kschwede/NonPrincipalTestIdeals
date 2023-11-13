
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
--also may want to rename uBound and lBound

tIdeal = (I,t,e0,f0)->( ---I an ideal, t=a/p, and  e0, f0 natural numbers saying how long to run 
    p:=char ring I;
    RI:=reesAlgebra I;
    tau:=sub((testModule(first flattenRing RI))#0,RI);
    G:=divisor(sub(I,RI));
    e1:=1;
    uBound:=frobeniusRoot(1,{ceiling(t*(p))},{I});
    uBound1:={};
    for i from 1 to e0 do(
	e1=i;
	uBound1=uBound;
	uBound=frobeniusRoot(i+1,{ceiling(t*((p)^(i+1)))},{I});
	if uBound1==uBound then break;
	);
    f1:=0;
    lBound:={};
    for j from 1 to f0 do(
	f1=j;
	lBound=frobeniusRoot(j,embedAsIdeal(prune HH_0(directImageComplex (tau*ideal(p^j*t*G)*RI^1))));
    	if lBound==uBound then break;
	);
    return (lBound,e1,f1) 
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
