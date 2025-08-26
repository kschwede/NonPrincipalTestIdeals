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
R = QQ[x,y];
J = ideal(x,y);
S = classicalReesAlgebra(J);
T = extendedReesAlgebra(J);

omegaS = reesCanonicalModule(S);
omegaSIdeal = reesModuleToIdeal()
omegaT = reesCanonicalModule(T);