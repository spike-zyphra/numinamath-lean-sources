import Mathlib

/- Applied to a bill for $10,000 the difference between a discount of 40% and two successive discounts 
of 36% and 4%,expressed in dollars, is:
(A)0  (B)144  (C)256  (D)400  (E)416 -/
theorem algebra_98009 (x : ℝ) (hx : x = 10000) :
x * (1 - 36 / 100) * (1 - 4 / 100)- x * (1 - 40 / 100) = 144 := by 
 -- The claims comes from substitution of the value for x plus algebraic calculations.
  rw[hx]
  ring_nf