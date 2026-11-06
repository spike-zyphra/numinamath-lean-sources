import Mathlib

theorem inequalities_600525 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a^2 + b^2) / (2 * a * b) + 2 * Real.sqrt (a * b) / (a + b) ≥ 2 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : Real.sqrt (a * b) > 0 := by
    apply Real.sqrt_pos.mpr
    positivity
  have h3 : 0 < a + b := by linarith
  have h4 : (a ^ 2 + b ^ 2) / (2 * a * b) + 2 * Real.sqrt (a * b) / (a + b) - 2 ≥ 0 := by
    have h5 : (a ^ 2 + b ^ 2) / (2 * a * b) + 2 * Real.sqrt (a * b) / (a + b) - 2 =
        ((a ^ 2 + b ^ 2) * (a + b) + 4 * a * b * Real.sqrt (a * b) - 4 * a * b * (a + b)) / (2 * a * b * (a + b)) := by 
      field_simp
      ring
    rw [h5]
    have h6 : 0 < (2 * a * b * (a + b) : ℝ) := by positivity
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (Real.sqrt (a * b) - a / 2), sq_nonneg (Real.sqrt (a * b) - b / 2), sq_nonneg (a + b - 2 * Real.sqrt (a * b)), sq_nonneg (Real.sqrt (a * b) ^ 2 - a * b), Real.sqrt_nonneg (a * b), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by nlinarith), sq_nonneg (a - Real.sqrt (a * b)), sq_nonneg (b - Real.sqrt (a * b)),
        mul_pos ha hb, mul_pos ha h1, mul_pos hb h1, sq_nonneg (a - b),
        mul_pos (show 0 < a + b by linarith) (show 0 < a * b by positivity)]
    all_goals positivity
  linarith