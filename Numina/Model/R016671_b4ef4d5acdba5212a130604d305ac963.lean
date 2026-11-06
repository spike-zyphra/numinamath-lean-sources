import Mathlib

open Real

theorem inequalities_46212 {a b c : ℝ} (ha : 1 < a) (hb : a ≤ b) (hc : b ≤ c) :
    logb a b + logb b c + logb c a ≤ logb b a + logb c b + logb a c := by 
  have h1 : 1 < b := by linarith
  have h2 : 1 < c := by linarith
  have h3 : logb a b = log b / log a := by field_simp [logb]
  have h4 : logb b c = log c / log b := by field_simp [logb]
  have h5 : logb c a = log a / log c := by field_simp [logb]
  have h6 : logb b a = log a / log b := by field_simp [logb]
  have h7 : logb c b = log b / log c := by field_simp [logb]
  have h8 : logb a c = log c / log a := by field_simp [logb]
  rw [h3, h4, h5, h6, h7, h8]
  have h9 : 0 < log a := by
    have h : log a > 0 := by
      apply log_pos
      linarith
    linarith
  have h10 : 0 < log b := by
    have h : log b > 0 := by
      apply log_pos
      linarith
    linarith
  have h11 : 0 < log c := by
    have h : log c > 0 := by
      apply log_pos
      linarith
    linarith
  have h12 : log a ≤ log b := by
    apply Real.log_le_log
    linarith
    linarith
  have h13 : log b ≤ log c := by
    apply Real.log_le_log
    linarith
    linarith
  have h14 : log b ^ 2 * log c + log a * log c ^ 2 + log a ^ 2 * log b ≤ log a ^ 2 * log c + log b ^ 2 * log a + log c ^ 2 * log b := by
    have h15 : log b ≤ log c := by
      apply Real.log_le_log
      linarith
      linarith
    have h16 : log a ≤ log b := by
      apply Real.log_le_log
      linarith
      linarith
    nlinarith [sq_nonneg (log a - log b), sq_nonneg (log b - log c), sq_nonneg (log a - log c),
              mul_nonneg (by linarith : (0 : ℝ) ≤ log b - log a) (by linarith : (0 : ℝ) ≤ log c - log b),
              mul_nonneg (show 0 ≤ log a by linarith) (show 0 ≤ log b - log a by nlinarith),
              mul_nonneg (show 0 ≤ log b - log a by nlinarith) (show 0 ≤ log c - log b by nlinarith),
              mul_nonneg (show 0 ≤ log a by linarith) (show 0 ≤ log c - (log b) by nlinarith)]
  have h17 : log b / log a + log c / log b + log a / log c - (log a / log b + log b / log c + log c / log a) ≤ 0 := by
    have h22 : (log b / log a + log c / log b + log a / log c) - (log a / log b + log b / log c + log c / log a) =
        (log b ^ 2 * log c + log a * log c ^ 2 + log a ^ 2 * log b - (log a ^ 2 * log c + log b ^ 2 * log a + log c ^ 2 * log b)) / (log a * log b * log c) := by
      field_simp
      ring
    have h23 : log a * log b * log c > 0 := by
      positivity
    have h24 : log b ^ 2 * log c + log a * log c ^ 2 + log a ^ 2 * log b - (log a ^ 2 * log c + log b ^ 2 * log a + log c ^ 2 * log b) ≤ 0 := by
      nlinarith
    have h25 : (log b ^ 2 * log c + log a * log c ^ 2 + log a ^ 2 * log b - (log a ^ 2 * log c + log b ^ 2 * log a + log c ^ 2 * log b)) / (log a * log b * log c) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      all_goals positivity
    linarith [h22, h25]
  linarith