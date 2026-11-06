import Mathlib
open Real

/- Alice sells an item at 10$ less than the list price and receives 10% of her selling price as her
commission. Bob sells the same item at
20$ less than the list price and receives 20% of his selling price as his commission.
If they both get the same commission, then the list price is
(A) $20 (B) $30 (C) $50 (D) $70 (E) $100 -/
theorem algebra_94877 {x : ℝ} (h : (x - 10) * (10 / 100) = (x - 20) * (20 / 100)) :
x = 30 := by
  -- solving the linear equation
  linarith