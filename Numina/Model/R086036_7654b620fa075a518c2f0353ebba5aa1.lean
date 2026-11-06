import Mathlib

theorem algebra_319752 (α : ℝ) (h : Real.sin α + Real.cos α = 1 / 5) :
    abs (Real.sin α - Real.cos α) = 7 / 5 := by 
  have h1 : (Real.sin α + Real.cos α)^2 = 1 / 25 := by
    rw [h]
    norm_num
  have h2 : (Real.sin α - Real.cos α) ^ 2 = 49 / 25 := by 
    have h_identity : (Real.sin α + Real.cos α)^2 + (Real.sin α - Real.cos α)^2 = 2 := by 
      nlinarith [Real.sin_sq_add_cos_sq α]
    rw [h1] at h_identity 
    nlinarith 
  have h3 : abs (Real.sin α - Real.cos α) = 7 / 5 := by 
    have h4 : (Real.sin α - Real.cos α) ^ 2 = 49 / 25 := h2 
    have h5 : abs (Real.sin α - Real.cos α) = Real.sqrt ((Real.sin α - Real.cos α) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h5, h4]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> linarith [show (0 : ℝ) ≤ (7 / 5) by norm_num, show (0 : ℝ) ≤ (49 / 25) by norm_num]
  exact h3