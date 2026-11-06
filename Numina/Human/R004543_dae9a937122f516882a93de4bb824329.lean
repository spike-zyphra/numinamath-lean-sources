import Mathlib

/- 2. Subtract 1 from the number $M$, multiply by $\frac{2}{3}$, add 8, and then divide by 7, to get 4. Find $M$.

-/
theorem algebra_281275 (M : ℝ) (h : (2 / 3 * (M - 1) + 8) / 7 = 4) : M = 31 := by
  field_simp at h
  linarith