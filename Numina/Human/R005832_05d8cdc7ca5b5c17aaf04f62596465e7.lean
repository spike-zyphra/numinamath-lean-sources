import Mathlib
/- Compute the value of $\sqrt{105^{3}-104^{3}}$, given that it is a positive integer. -/
theorem number_theory_610145 : √(105 ^ 3 - 104 ^ 3) = 181:= by
  -- First, we expand the expression
  ring_nf
  -- Then, we simplify the expression
  rw [show √32761 = √(181 ^ 2) by norm_num]
  -- Finally, we simplify the expression
  field_simp
