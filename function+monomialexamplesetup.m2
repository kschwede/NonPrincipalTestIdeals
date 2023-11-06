restart

--Here is a function automating the process from the proof of concept file
--certainly NOT optimized but can be used for testing


------------------
needsPackage"BGG"
needsPackage"ReesAlgebra"
needsPackage"TestIdeals"
needsPackage"Divisor"

-------------------------------

tIdeal = (I,t,e0,f0)->( ---I an ideal, t=a/p^e, and  e0, f0 natural numbers saying how long to run
    p:=char ring I;
    RI:=reesAlgebra I;
    tau:=sub((testModule(first flattenRing RI))#0,RI);
    G:=divisor(sub(I,RI));
    e1:=0;
    for i from 1 to e0 do(
	e1=i;
	if frobeniusRoot(i,{ceiling(t* ((p)^i-1))},{I})==frobeniusRoot(i+1,{ceiling(t* ((p)^(i+1)-1))},{I}) then break;
	);
    uBound:=frobeniusRoot(e1,{ceiling(t* ((p)^e1-1))},{I});
    f1:=0;
    for j from e1 to f0 do(
	f1=j;
    	if frobeniusRoot(j,embedAsIdeal(prune HH_0(directImageComplex (tau*ideal(p^j*t*G)*RI^1))))==uBound then break;
	);
    lBound:=frobeniusRoot(f1,embedAsIdeal(prune HH_0(directImageComplex (tau*ideal(p^f1*t*G)*RI^1))));
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
tIdeal(Jp,t,5,5)----this is kind of slow
multiplierIdeal( monomialIdeal J0,t)

-------

