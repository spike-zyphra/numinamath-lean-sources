import Mathlib

/- In a recent basketball game, Shenille attempted only three-point shots and two-point shots. 
She was successful on 20% of her three-point shots and 30% of her two-point shots. 
Shenille attempted 30 shots. How many points did she score?
(A) 12(B) 18(C) 24(D) 30(E) 36 -/
theorem algebra_95681 (x : ℕ) (x3 x2 : ℚ) 
(hx : x3 = 3 * 20/100 * x ) 
(hy : x2 = 2 * 30/100 * (30-x)):
x3 + x2 = 18 := by
--we call x the 3 point shots made. Then we have a system of 3 equations in 3 indeterminates that we can solve using arithmetic tactics.
rw[hx, hy]
ring