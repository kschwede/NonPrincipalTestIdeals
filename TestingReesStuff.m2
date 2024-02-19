restart
loadPackage("Divisor", DebuggingMode=>true)
loadPackage "NonPrincipalTestIdeals"
R = QQ[x,y,z]
J = ideal(x^2,y,z)
S = extendedReesAlgebra(J)
describe S
I = trim ((ideal(S#"Degree1"))^3 + ideal((S#"Degree1")#0)  + (ideal((S#"Degree1")#1))^2)
trim gradedReesPiece(2,I)


ideal S
omegaM = canonicalModule(S)
ann omegaM == ideal S
I = reesModuleToIdeal(S, omegaM, IsGraded => true, ReturnMap => true)