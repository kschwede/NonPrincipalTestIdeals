restart

needsPackage"BGG"
needsPackage"ReesAlgebra"
needsPackage"TestIdeals"
needsPackage"Divisor"


--------Example 1
R=ZZ/3[x,y,z];
I=ideal(x^2,x*y,y^2);

---setup
S=reesAlgebra I
gensS=flatten flatten append(entries vars S,entries vars R)
tau1=(testModule(first flattenRing S))#0
tau1'=sub(tau1,S)
G=divisor(sub(I,S))

------computing tau(I^t) t=5/3
p=char R;t=5/p;

e=1
uBound=frobeniusRoot(e,{ceiling (t*p^e)},{I})---stable immediately 

f=2
stuff=tau1'*ideal(p^f*t*G)*S^1;
lBound=frobeniusRoot(f,embedAsIdeal(prune HH_0(directImageComplex stuff)))--stable at f=2

uBound==lBound
---- 
-------Another example:I_2(2x3)
R=ZZ/3[a_1..a_6];
I=minors(2,genericMatrix(R,2,3));
fptI=2;

---setup (Ex 2)
S=reesAlgebra I
gensS=flatten flatten append(entries vars S,entries vars R)
tau1=(testModule(first flattenRing S))#0
tau1'=sub(tau1,S)
G=divisor(sub(I,S))

------computing tau(I^t) t=10/3
p=char R;t=10/p;
tIdeal=I^(floor(t)-fptI+1)-- from Henriques paper
e=1
uBound1=frobeniusRoot(e,{ceiling (t*p^e)},{I})---stable immediately 

f=1
stuff=tau1'*ideal(p^f*t*G)*S^1;
lBound=frobeniusRoot(f,embedAsIdeal(prune HH_0(directImageComplex stuff)))--stable immediately

uBound==lBound
