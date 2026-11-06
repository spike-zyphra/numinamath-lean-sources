import Mathlib

theorem algebra_14641 {x : ℝ} (hx : 0 < x) (h : Real.logb 2 (x^2) + Real.logb (1 / 2) x = 5) :
    x = 32 := by 
  have h1 : Real.logb 2 (x^2) = 2 * Real.logb 2 x := by
    simp [Real.logb_pow]
  have h2 : Real.logb (1 / 2) x = - Real.logb 2 x := by 
    have h3 : Real.logb (1 / 2) x = Real.logb 2 x / Real.logb 2 (1 / 2) := by 
      field_simp [Real.logb]
    have h4 : Real.logb 2 (1 / 2) = -1 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h4] at h3
    rw [h3]
    <;> ring
  rw [h1, h2] at h
  have h_eq : Real.logb 2 x = 5 := by 
    linarith
  have hx2 : x = (2 : ℝ) ^ 5 := by 
    rw [Real.logb_eq_iff_rpow_eq] at h_eq 
    · nlinarith 
    all_goals linarith
  norm_num at hx2 ⊢ 
  exact hx2