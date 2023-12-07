
restart
needsPackage"Divisor"
needsPackage"TestIdeals"

tIdeal= (I,t)->(
    S:=reesAlgebra I;
    --mu:=rank source gens I;
    pr:=map(ring I,S,apply(rank source gens I, i->0));
    tauS:=sub(first testModule first flattenRing S,S);
    f:=basis(t-1,image gens tauS);
    return(embedAsIdeal prune coker pr(gens ker f));
    )
    
-----Test for monomial ideals    
    
needsPackage"MultiplierIdeals"
needsPackage"RandomIdeals"
R=ZZ[x,y,z];
tmax=5;p=3;mu=3; d=2;

for e from 1 to 10 do(
t=random(1,tmax);
L=apply(mu, i -> random(2,d));
I=randomMonomialIdeal(L,R);
m0=multiplierIdeal(monomialIdeal(sub(I,R**QQ)),t);
Rp=ZZ/p[x,y,z];
tp=tIdeal(sub(I,Rp),t);
print(e,sub(tp,R)==sub(m0,R), I);
)


--Failure exampls
use R
J=ideal(y*z,x*y,y^2)
--J=ideal(x*y^3,x*z^3,x^3*y)
--J=ideal(x*z,z^2,x^2*z)
--J=ideal(x*y,y^2*z^2,y^5)
--J=ideal(z^2,y^2*z,x^4,x^3*y,y^4)

J'=sub(J,ZZ/p[x,y,z])
presentation image gens J'
m0=multiplierIdeal(monomialIdeal(sub(J,R**QQ)),4)
tp=tIdeal(J',4)

sub(tp,R)==sub(m0,R)
t=3
S=reesAlgebra(J')
ideal S
embedAsIdeal (OO canonicalDivisor(first flattenRing S,IsGraded=>true),IsGraded=>true)

testModule first flattenRing S
mu=rank source gens J';
pr=map(ring J',S,apply(rank source gens J', i->0))

tauS=sub(first testModule first flattenRing S,S)
f=basis(2,tauS*S^1)
embedAsIdeal prune coker pr(gens ker f)

needsPackage"BernsteinSato"
multiplierIdeal(sub(J,R**QQ),2)

