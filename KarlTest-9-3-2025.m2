restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals" 
installPackage "NonPrincipalTestIdeals"
check NonPrincipalTestIdeals

restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
R = ZZ/7[x,y,z];
m = ideal(x,y,z);
assert(isFJumpingExponent(5/2, m) == false);
assert(isFJumpingExponent(3, m) == true);
assert(isFJumpingExponent(4, m) == true);

S = ZZ/5[a,b];
J = (ideal(a,b))*(ideal(a^2,b))^2;--this is a monomial ideal, we know the log resolution, computing by hand means that the lct = fpt should be min(2/3,3/5) = 3/5.
L = testModule(3/5, J)
assert((ideal(a,b))*(L#1) == L#0)
K = testModuleMinusEpsilonNP(3/5, J)
assert(K#1 == K#0)
isFJumpingExponent(3/5, J)


restart
loadPackage "NonPrincipalTestIdeals"
R = ZZ/5[x,y];
m = ideal((x-1)^2,y^2);
S = classicalReesAlgebra(m)
T = extendedReesAlgebra(m)
reesCanonicalModule(S)
reesCanonicalModule(T)
testModule(11/10, m)
testModule(1, m)

R = ZZ/5[x,y];
m = ideal((x-1),y);
S = classicalReesAlgebra(m)
T = extendedReesAlgebra(m)
reesCanonicalModule(S)
loadPackage "NonPrincipalTestIdeals"
reesCanonicalModule(T)


loadPackage "NonPrincipalTestIdeals"
R = ZZ/7[x,y,z]/ideal(x*y-z^2); --threshold should be 1
J = ideal(x,y,z);
isFPT(1/1,J)



restart
loadPackage "NonPrincipalTestIdeals"
R = QQ[x,y];
m = ideal((x-1)^2,(y-2)^3);
S = classicalReesAlgebra(m)
T = extendedReesAlgebra(m)
reesCanonicalModule(S)
reesCanonicalModule(T)


restart
loadPackage "NonPrincipalTestIdeals"
            R = ZZ/3[x,y,z];
            I = ideal(x^2,y^3,z^5); --fpt should be 1/2 + 1/3 + 1/5 = 31/30
            isFPT(31/30, I)
            isFRationalThreshold(31/30, I)
            isFRationalThreshold(1, I, Verbose=>true)
            isFPT(1, I)

restart
loadPackage "NonPrincipalTestIdeals"
R = ZZ/3[u,v]
I = ideal( (u-1)^2, v^3) --fpt should be 1/2+1/3 = 5/6, but it's not at the origin
isFPT(5/6, I)
isFPT(5/6, I, AtOrigin=>true, Verbose=>true)