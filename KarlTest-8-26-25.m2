restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"


--checking basics
R = QQ[x,y];
J = ideal(x,y);
S = classicalReesAlgebra(J);
T = extendedReesAlgebra(J);
--we check gradedReesPiece

IS = ideal(1_S);
base = gradedReesPiece(0, IS);
use R
assert(base*(ideal(x,y))^1 == gradedReesPiece(1, IS))
assert(base*(ideal(x,y))^3 == gradedReesPiece(3, IS))

IT = ideal(1_T);
base = gradedReesPiece(0, IT);
assert(base == gradedReesPiece(-1, IT))
assert(base == gradedReesPiece(-3, IT))
assert(base*(ideal(x,y))^1 == gradedReesPiece(1, IT))
assert(base*(ideal(x,y))^3 == gradedReesPiece(3, IT))


R = QQ[a,b,c];
J = (ideal(a,b,c))^2;
S = classicalReesAlgebra(J);
T = extendedReesAlgebra(J);
IS = ideal(1_S);
base = gradedReesPiece(0, IS);
use R
assert(base*(ideal(a,b,c))^2 == gradedReesPiece(1, IS))
assert(base*(ideal(a,b,c))^6 == gradedReesPiece(3, IS))


IT = ideal(1_T);
base = gradedReesPiece(0, IT);
assert(base == gradedReesPiece(-1, IT))
assert(base == gradedReesPiece(-3, IT))
assert(base*(ideal(a,b,c))^2 == gradedReesPiece(1, IT))
assert(base*(ideal(a,b,c))^6 == gradedReesPiece(3, IT))

restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
installPackage "NonPrincipalTestIdeals"
check NonPrincipalTestIdeals



restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
--now we check canonical modules and reesModuleToIdeal
R = QQ[x,y,z];
J = ideal(x,y,z);
S = classicalReesAlgebra(J);
omegaS = reesCanonicalModule(S);
(omegaSIdeal, d, phi ) =  reesModuleToIdeal(S, omegaS);
degShift = d#0; --this is how far we have to shift
assert(0 == trim gradedReesPiece(0+degShift, omegaSIdeal)); -- the a invariant of the Rees algebra should be -1, so this should be zero.
baseOmega = trim gradedReesPiece(1+degShift, omegaSIdeal);  --this should be a free module
assert(isLocallyPrincipalIdeal(baseOmega)); --this is a Gorenstein rational singularity
assert(baseOmega == trim gradedReesPiece(2+degShift, omegaSIdeal)); --discrepancy 2, so nothing should change
use R;
assert((ideal(x,y,z))*baseOmega == trim gradedReesPiece(3+degShift, omegaSIdeal)); --but we should get a jump here.
T = extendedReesAlgebra(J);
omegaT = reesCanonicalModule(T);
(omegaTIdeal, d, psi ) =  reesModuleToIdeal(T, omegaT);
degShift = d#0; --this is how far we have to shift
baseOmega = trim gradedReesPiece(-10+degShift, omegaTIdeal);  --this should be a free module
assert(isLocallyPrincipalIdeal(baseOmega));
assert(baseOmega == trim gradedReesPiece(1+degShift, omegaTIdeal));
assert(baseOmega == trim gradedReesPiece(2+degShift, omegaTIdeal));
use R;
assert((ideal(x,y,z))*baseOmega == trim gradedReesPiece(3+degShift, omegaTIdeal)); --but we should get a jump here.
