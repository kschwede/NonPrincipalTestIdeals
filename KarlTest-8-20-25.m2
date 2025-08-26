restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
R = ZZ/7[x,y,z]
J = ideal(x^2,y,z)
S = classicalReesAlgebra(J)
T = extendedReesAlgebra(J)
debugLevel = 2;
reesCanonicalModule(S)
reesCanonicalModule(T)


restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
R = ZZ/7[x,y,z,w]
J = ideal(x,y,z,w)
S = classicalReesAlgebra(J)
T = extendedReesAlgebra(J)
debugLevel = 2;
reesCanonicalModule(S)
reesCanonicalModule(T)

restart
uninstallPackage "NonPrincipalTestIdeals"
loadPackage "NonPrincipalTestIdeals"
R = ZZ/7[x,y]
J = ideal(x,y)
S = classicalReesAlgebra(J)
T = extendedReesAlgebra(J)
debugLevel = 2;
reesCanonicalModule(S)
reesCanonicalModule(T)