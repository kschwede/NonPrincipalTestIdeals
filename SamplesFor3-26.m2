restart
loadPackage "NonPrincipalTestIdeals";
loadPackage "MultiplierIdeals";

R = ZZ/5[x,y,z]
I = ideal(x^2,y^3,z^4)
elapsedTime testIdealNP(5/4, I)
elapsedTime testIdealNP(26/25, I)
elapsedTime testIdealNP(13/12, I)
isFJumpingExponentNP(13/12, I)

S = QQ[a,b,c] 
J = monomialIdeal(a^2,b^3,c^4)
elapsedTime multiplierIdeal(J, 5/4)
elapsedTime multiplierIdeal(J, 13/12)
elapsedTime multiplierIdeal(J, 26/25)

restart
loadPackage "NonPrincipalTestIdeals";
R = ZZ/5[x,y,z]
I2 = ideal(x^3+y^3, y^4, z^2)
trim elapsedTime testIdealNP(8/5, I2)

needsPackage "Dmodules"
S = QQ[a,b,c];
J2 = ideal(a^3+b^3,b^4,c^2)
elapsedTime multiplierIdeal(J2, 8/5)


restart
R = ZZ/3[x,y,z]/ideal(x^2-y*z)

R = 

