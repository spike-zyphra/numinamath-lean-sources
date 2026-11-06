import Mathlib

theorem algebra_16928 : 2 / Real.logb 4 (2000 ^ 6) + 3 / Real.logb 5 (2000 ^ 6) = 1 / 6 := by
  have h1 : Real.logb 4 (2000 ^ 6) = (6 * Real.log (2000 : ℝ)) / Real.log (4 : ℝ) := by
    field_simp [Real.logb]
    <;> ring_nf <;> simp [Real.log_pow]
    <;> all_goals linarith
  have h2 : Real.logb 5 (2000 ^ 6) = (6 * Real.log (2000 : ℝ)) / Real.log (5 : ℝ) := by
    field_simp [Real.logb]
    <;> ring_nf <;> simp [Real.log_pow]
    <;> all_goals linarith
  rw [h1, h2]
  have h3 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h4 : Real.log (2000 : ℝ) = 4 * Real.log (2 : ℝ) + 3 * Real.log (5 : ℝ) := by
    rw [show (2000 : ℝ) = 2^4 * 5^3 by norm_num]
    simp [Real.log_mul, Real.log_pow]
    all_goals linarith
  rw [h3, h4]
  have h6 : Real.log (2 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h7 : Real.log (5 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h8 : (4 * Real.log (2 : ℝ) + 3 * Real.log (5 : ℝ)) > 0 := by
    nlinarith [Real.log_pos (show (5 : ℝ) > 1 by norm_num : (5 : ℝ) > 1), Real.log_pos (show (2 : ℝ) > 1 by norm_num : (2 : ℝ) > 1)]
  field_simp [(show (4 * Real.log (2 : ℝ) + 3 * Real.log (5 : ℝ)) ≠ 0 by linarith)]
  <;> ring_nf <;> field_simp <;> ring
  all_goals nlinarith [Real.log_pos (show (5 : ℝ) > 1 by norm_num : (5 : ℝ) > 1), Real.log_pos (show (2 : ℝ) > 1 by norm_num : (2 : ℝ) > 1)]