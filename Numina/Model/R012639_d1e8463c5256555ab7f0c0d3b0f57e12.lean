import Mathlib

open Real

theorem algebra_149625 (a : ℝ) (ha : 1 < a) :
    logb a 16 + 2 * logb 4 a ≥ 4 := by
  have h1 : logb a 16 = log 16 / log a := by
    field_simp [logb]
  have h2 : log 16 = 4 * log 2 := by
    calc
      log 16 = log ((2: ℝ) ^4) := by norm_num
      _ = 4 * log 2 := by simp [log_pow]
  have h3 : logb a 16 = 4 * log 2 / log a := by
    rw [h1, h2]
  have h4 : logb 4 a = log a / log (4: ℝ) := by
    field_simp [logb]
  have h5 : log (4: ℝ) = 2 * log 2 := by
    calc
      log (4: ℝ) = log ((2: ℝ) ^2) := by norm_num
      _ = 2 * log 2 := by simp [log_pow]
  have h6 : 2 * logb 4 a = log a / log 2 := by
    rw [h4, h5]
    field_simp
    <;> linarith
  have h7 : logb a 16 + 2 * logb 4 a = 4 * log 2 / log a + log a / log 2 := by
    rw [h3, h6]
  have h8 : log a > 0 := by
    apply log_pos
    linarith
  have h9 : log 2 > 0 := by
    apply log_pos
    norm_num
  have h10 : 4 * log 2 / log a + log a / log 2 ≥ 4 := by
    have h11 : log a > 0 := h8
    have h12 : log 2 > 0 := h9
    have h13 : log a * log 2 > 0 := mul_pos h11 h12
    have h14 : (log a - 2 * log 2) ^2 ≥ 0 := sq_nonneg (log a - 2 * log 2)
    have h17 : (4 * log 2 / log a + log a / log 2 - 4) ≥ 0 := by
      have h18 : log a * log 2 > 0 := h13
      have h19 : (4 * log 2 / log a + log a / log 2 - 4) = (4 * (log 2) ^2 + (log a) ^2 - 4 * (log a) * (log 2)) / (log a * log 2) := by
        field_simp
        <;> ring
      rw [h19]
      have h20 : 4 * (log 2) ^2 + (log a) ^2 - 4 * (log a) * (log 2) ≥ 0 := by
        nlinarith [h14]
      apply div_nonneg
      linarith
      all_goals linarith
    linarith
  linarith [h7, h10]