import Mathlib

/- Simplify and rationalize the denominator: $$\frac{1}{1+ \frac{1}{\sqrt{3}+1}}.$$ -/
theorem algebra_10248 : 1 / (1 + 1 / (Real.sqrt 3 + 1)) = Real.sqrt 3 - 1 := by 
  field_simp
  ring
  field_simp
  ring_nf