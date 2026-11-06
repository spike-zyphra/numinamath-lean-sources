import Mathlib

theorem algebra_321408 (x : ℝ) : 3 * x ^ 3 - 4 * x + 1 = 3 * (x - 1) * (x + (3 - Real.sqrt 21) / 6) * (x + (3 + Real.sqrt 21) / 6) := by
  ring_nf
  have h1 : Real.sqrt 21 ^ 2 = 21 := by
    norm_num [Real.sq_sqrt]
  simp [h1]
  <;> nlinarith [Real.sqrt_nonneg 21]