import Mathlib

/- Kyle found the sum of the digits of $2014^{2014}$. Then, Shannon found the sum of the digits of Kyle's result. Finally, James found the sum of the digits of Shannon's result. What number did James find?

$\text{(A) }5\qquad\text{(B) }7\qquad\text{(C) }11\qquad\text{(D) }16\qquad\text{(E) }18$ -/
theorem number_theory_59160 : (Nat.digits 10 ((Nat.digits 10 (Nat.digits 10 (2014^2014)).sum).sum)).sum = 7 := by 
  native_decide