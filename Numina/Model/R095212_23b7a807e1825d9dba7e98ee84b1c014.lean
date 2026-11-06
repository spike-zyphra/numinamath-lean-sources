import Mathlib

theorem inequalities_142220 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : ((a + b) / 2) ^ 2 ≥ a * b := by
    nlinarith [sq_nonneg (a - b), mul_pos ha hb]

  have h4 : Real.sqrt (a * b) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    nlinarith [show 0 ≤ a * b by positivity]

  have h5 : (a + b) / 2 ≥ Real.sqrt (a * b) := by
    nlinarith [Real.sqrt_nonneg (a * b), show 0 ≤ (a + b)/2 by nlinarith, sq_nonneg ((a + b) / 2 - Real.sqrt (a * b)), h4, h2]

  exact h5