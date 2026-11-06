import Mathlib

theorem algebra_2192 (M : ℝ) (h : ((-1)^3 + 2 - M^2) / (-3 - (-1)^2) = 2) :
    M = 3 ∨ M = -3 := by
  have h1 : (-3 - (-1 : ℝ) ^ 2) ≠ 0 := by 
    norm_num
  have eq1 : (-1 : ℝ) ^ 3 + 2 - M ^ 2 = 2 * (-3 - (-1 : ℝ) ^ 2) := by
    field_simp [h1] at h
    linarith 
  have eq2 : (-1 : ℝ) ^ 3 + 2 - M ^ 2 = -8 := by
    norm_num at eq1 ⊢
    linarith 
  have eq3 : M ^ 2 = 9 := by 
    nlinarith 
  have h2 : M = 3 ∨ M = -3 := by
    have h3 : M ^ 2 = 9 := eq3
    have h4 : M = 3 ∨ M = -3 := by
      apply eq_or_eq_neg_of_sq_eq_sq 
      norm_num 
      linarith
    exact h4 
  exact h2