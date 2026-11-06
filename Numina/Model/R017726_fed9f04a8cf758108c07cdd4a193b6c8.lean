import Mathlib

open Real

theorem algebra_119503 : (logb 5 6) * (logb 6 7) * (logb 7 8) * (logb 8 9) * (logb 9 10) ∈ Set.Ioo 1 2 := by
  have h1 : (logb 5 6) * (logb 6 7) * (logb 7 8) * (logb 8 9) * (logb 9 10) = (log 10) / (log 5) := by
    have h2 : logb 5 6 = log 6 / log 5 := by field_simp [logb]
    have h3 : logb 6 7 = log 7 / log 6 := by field_simp [logb]
    have h4 : logb 7 8 = log 8 / log 7 := by field_simp [logb]
    have h5 : logb 8 9 = log 9 / log 8 := by field_simp [logb]
    have h6 : logb 9 10 = log 10 / log 9 := by field_simp [logb]
    rw [h2, h3, h4, h5, h6]
    field_simp
    <;> ring
  rw [h1]
  have h2 : log 5 > 0 := by
    apply log_pos
    norm_num
  have h3 : log 10 > log 5 := by
    apply Real.log_lt_log
    all_goals norm_num
  have h4 : log 10 < 2 * log 5 := by
    have h5 : log 25 = 2 * log 5 := by
      calc
        log 25 = log (5 ^ 2) := by norm_num
        _ = 2 * log 5 := by simp [log_pow]
    have h6 : log 10 < log 25 := by
      apply Real.log_lt_log
      all_goals norm_num
    linarith [h5, h6]
  constructor
  · -- Show that 1 < (log 10) / (log 5)
    have h7 : log 10 > log 5 := h3
    have h8 : (log 10) / (log 5) > 1 := by
      have h9 : log 5 > 0 := h2
      have h10 : log 10 > log 5 := h7
      have h11 : (log 10) / (log 5) > (log 5) / (log 5) := by
        apply (div_lt_div_right h9).mpr
        linarith
      have h13 : (log 5) / (log 5) = 1 := by
        field_simp [h2]
      linarith [h13, h11]
    linarith
  · -- Show that (log 10) / (log 5) < 2
    have h8 : log 10 < 2 * log 5 := h4
    have h6 : (log 10) / (log 5) < 2 := by
      apply (div_lt_iff₀ h2).mpr
      linarith
    linarith