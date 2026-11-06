import Mathlib

theorem algebra_188412 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : Real.logb 2 x + Real.logb 4 y = 4) (h2 : Real.logb 4 x + Real.logb 2 y = 5) :
    x = 4 ∧ y = 16 := by

  have h3 : Real.logb 4 y = Real.logb 2 y / 2 := by
    have h4 : Real.logb 4 y = Real.logb 2 y / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h5 : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h4, h5]

  have h6 : Real.logb 4 x = Real.logb 2 x / 2 := by
    have h7 : Real.logb 4 x = Real.logb 2 x / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h8 : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h7, h8]

  rw [h3] at h1
  rw [h6] at h2

  have eq1 : 2 * Real.logb 2 x + Real.logb 2 y = 8 := by
    linarith [h1]

  have eq2 : Real.logb 2 x + 2 * Real.logb 2 y = 10 := by
    linarith [h2]

  have h9 : Real.logb 2 x = 2 := by
    linarith [eq1, eq2]

  have hx' : x = 4 := by
    have h9' : x = (2 : ℝ) ^ Real.logb 2 x := by
      field_simp [Real.rpow_logb, show (2 : ℝ) > 0 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, hx]
    rw [h9] at h9'
    norm_num at h9' ⊢
    exact h9'

  have h10 : Real.logb 2 y = 4 := by
    linarith [eq1, h9]

  have hy' : y = 16 := by
    have h10' : y = (2 : ℝ) ^ Real.logb 2 y := by
      field_simp [Real.rpow_logb, show (2 : ℝ) > 0 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, hy]
    rw [h10] at h10'
    norm_num at h10' ⊢
    exact h10'

  exact ⟨hx', hy'⟩