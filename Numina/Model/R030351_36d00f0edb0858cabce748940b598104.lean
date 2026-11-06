import Mathlib

theorem algebra_183103 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + 2 * b = 6) :
    Real.log a + 2 * Real.log b ≤ 3 * Real.log 2 := by
  have h1 : a = 6 - 2 * b := by
    linarith
  have h3 : Real.log a + 2 * Real.log b = Real.log (a * (b ^ 2)) := by
    have h4 : Real.log a + 2 * Real.log b = Real.log a + Real.log (b ^ 2) := by
      have h7 : 2 * Real.log b = Real.log (b ^ 2) := by
        simp [Real.log_pow]
        <;> linarith
      linarith [h7]
    have h5 : Real.log a + Real.log (b ^ 2) = Real.log (a * (b ^ 2)) := by
      rw [Real.log_mul (by nlinarith) (by positivity)]
    rw [h4, h5]
  rw [h3]
  have h4 : a * (b ^ 2) ≤ (8 : ℝ) := by
    rw [show a = 6 - 2 * b by linarith]
    nlinarith [sq_nonneg (b - 2), sq_nonneg ((6 - 2 * b) - 2), sq_nonneg (b * (b - 2)), 
      mul_pos (show 0 < 6 - 2 * b by nlinarith) (show 0 < b by linarith), sq_nonneg (b - 2), sq_nonneg ((6 - 2 * b) - 2)]
  have h5 : Real.log (a * (b ^ 2)) ≤ Real.log (8 : ℝ) := by
    have h6 : a * (b ^ 2) > 0 := by
      apply mul_pos
      linarith
      positivity
    have h7 : (8 : ℝ) > 0 := by norm_num
    have h8 : a * (b ^ 2) ≤ (8 : ℝ) := h4
    have h9 : Real.log (a * (b ^ 2)) ≤ Real.log (8 : ℝ) := by
      apply Real.log_le_log
      all_goals nlinarith
    exact h9
  have h6 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    calc
      Real.log (8 : ℝ) = Real.log (2 ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by simp [Real.log_pow]
  linarith [h5, h6]