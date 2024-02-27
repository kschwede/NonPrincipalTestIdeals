restart
loadPackage("Divisor", DebuggingMode=>true)
loadPackage("TestIdeals", DebuggingMode=>true)
loadPackage "NonPrincipalTestIdeals"
R = ZZ/3[x,y]
J = ideal(x*y,x^2,y^2)
trim testIdealNP(4/3, J)
answer
break
testIdealNP(4/3, J)
answery
break
S = extendedReesAlgebra(J)
describe S
canonicalModule2 S
I = trim ((ideal(S#"Degree1"))^3 + ideal((S#"Degree1")#0)  + (ideal((S#"Degree1")#1))^2)
trim gradedReesPiece(2,I)


ideal S
omegaM = canonicalModule(S)
ann omegaM == ideal S
I = reesModuleToIdeal(S, omegaM, IsGraded => true, ReturnMap => true)