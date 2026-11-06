import Mathlib

theorem algebra_290839 (a b : ℝ)
    (ha : a = Real.logb 4 9) (hb : b = 108 * Real.logb 3 8) :
    ∃ n : ℤ, n^2 = a * b ∧ n = 18 := by
  use 18
  have ha1 : a = (Real.log 3 / Real.log 2) := by
    rw [ha]
    have h1 : Real.logb 4 9 = Real.log 9 / Real.log 4 := by
      field_simp [Real.logb]
    rw [h1]
    have h2 : Real.log 9 = 2 * Real.log 3 := by
      calc
        Real.log 9 = Real.log (3 ^ 2) := by norm_num
        _ = 2 * Real.log 3 := by simp [Real.log_pow]
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    rw [h2, h3]
    <;> field_simp <;> ring
  have hb1 : b = 324 * (Real.log 2 / Real.log 3) := by
    rw [hb]
    have h4 : Real.logb 3 8 = 3 * Real.logb 3 2 := by
      calc
        Real.logb 3 8 = Real.logb 3 (2 ^ 3) := by norm_num
        _ = 3 * Real.logb 3 2 := by simp [Real.logb_pow]
    have h5 : Real.logb 3 2 = (Real.log 2) / (Real.log 3) := by
      field_simp [Real.logb]
    rw [h4, h5]
    all_goals norm_num
    all_goals ring
  have h3 : a * b = 324 := by
    rw [ha1, hb1]
    have h4 : Real.log 2 ≠ 0 := by
      have : Real.log 2 > 0 := by apply Real.log_pos; all_goals linarith
      linarith
    have h5 : Real.log 3 ≠ 0 := by
      have : Real.log 3 > 0 := by apply Real.log_pos; all_goals linarith
      linarith
    field_simp [h4, h5]
    <;> nlinarith
  constructor
  · -- Show that (18:ℤ)^2 = a * b
    have h4 : (a * b : ℝ) = (324 : ℝ) := by
      linarith [h3]
    norm_num at h4 ⊢
    linarith
  · -- Show that n = 18
    rfl