import Mathlib

/- What is (20−(2010−201))+(2010−(201−20))?
(A) −4020(B) 0(C) 40(D) 401(E) 4020 -/
theorem algebra_93918 : ((20:ℤ) - ((2010:ℤ) - (201:ℤ))) + (2010:ℤ) - ((201:ℤ) - (20:ℤ)) = 40 := by ring 
--The claim is an algebraic calcularion in ℤ