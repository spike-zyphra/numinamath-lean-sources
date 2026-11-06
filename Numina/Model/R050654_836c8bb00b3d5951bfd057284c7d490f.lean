import Mathlib

open Real

theorem algebra_187669 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : logb 4 x - logb 2 y = 0) (h2 : x^2 - 5 * y^2 + 4 = 0) :
    (x = 1 ∧ y = 1) ∨ (x = 4 ∧ y = 2) := by
  have h3 : logb 4 x = logb 2 y := by 
    linarith 
  have h4 : logb 4 x = (logb 2 x) / (logb 2 (4 : ℝ)) := by 
    field_simp [logb]
  have h5 : logb 2 (4 : ℝ) = 2 := by 
    rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    <;> linarith
  rw [h4, h5] at h3 
  have h6 : logb 2 x = 2 * logb 2 y := by
    linarith 
  have h7 : logb 2 x = logb 2 (y ^ 2) := by
    rw [h6]
    simp [logb_pow]
    all_goals linarith 
  have h8 : x = y ^ 2 := by 
    have h9 : logb 2 x = logb 2 (y ^ 2) := h7 
    have h10 : x > 0 := by linarith 
    have h11 : y ^ 2 > 0 := by positivity 
    have h12 : x = (y ^ 2) := by 
      apply logb_injOn_pos (by norm_num) h10 h11 h9 
    nlinarith 
  have h9 : x = y ^ 2 := h8 
  rw [h9] at h2 
  have h11 : y^4 - 5 * y^2 + 4 = 0 := by 
    nlinarith [h2, sq_nonneg (y^2 - 1), sq_nonneg (y^2 - 4)]
  have h12 : (y ^ 2 - 1) * (y ^ 2 - 4) = 0 := by 
    nlinarith [h11]
  cases' (mul_eq_zero.mp h12) with h13 h14 
  · -- Case where $y^2 - 1 = 0$, so $y^2 = 1$
    have h15 : y ^ 2 = 1 := by linarith 
    have h16 : y = 1 := by 
      nlinarith 
    have h17 : x = 1 := by 
      rw [h16] at h9 
      nlinarith 
    left 
    exact ⟨h17, h16⟩ 
  · -- Case where $y^2 - 4 = 0$, so $y^2 = 4$
    have h18 : y ^ 2 = 4 := by linarith 
    have h19 : y = 2 := by 
      nlinarith 
    have h20 : x = 4 := by 
      rw [h19] at h9 
      nlinarith 
    right 
    exact ⟨h20, h19⟩