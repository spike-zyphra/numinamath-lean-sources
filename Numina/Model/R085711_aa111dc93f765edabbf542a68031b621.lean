import Mathlib

theorem algebra_321388 (a : ℝ) :
    a^4 - 14 * a^2 + 25 = (a + 1 + Real.sqrt 6) * (a + 1 - Real.sqrt 6) * (a - 1 + Real.sqrt 6) * (a - 1 - Real.sqrt 6) := by
  have h1 : Real.sqrt 6 ^ 2 = 6 := by
    rw [Real.sq_sqrt]
    norm_num
  have h2 : Real.sqrt 6 ^ 4 = 36 := by
    calc
      Real.sqrt 6 ^ 4 = (Real.sqrt 6 ^ 2) ^ 2 := by ring
      _ = 6 ^ 2 := by rw [h1]
      _ = 36 := by norm_num
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]