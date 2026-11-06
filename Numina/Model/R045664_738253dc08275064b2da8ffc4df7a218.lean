import Mathlib


theorem algebra_18701 (b : ℝ) (h : Real.sqrt ((4 - 1)^2 + (b - 2)^2) = 5) :
    b = 6 ∨ b = -2 := by
  have h1 : (4 - (1 : ℝ)) ^ 2 + (b - 2) ^ 2 = 25 := by
    calc
      (4 - (1 : ℝ)) ^ 2 + (b - 2) ^ 2 = (Real.sqrt ((4 - 1) ^ 2 + (b - 2) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (5 : ℝ) ^ 2 := by 
        rw [h]
      _ = (25 : ℝ) := by 
        norm_num
  have h2 : (b - 2) ^ 2 = 16 := by 
    nlinarith
  have h3 : b - 2 = 4 ∨ b - 2 = -4 := by 
    apply eq_or_eq_neg_of_sq_eq_sq 
    norm_num 
    linarith
  cases h3 with
  | inl h4 =>
    left 
    linarith 
  | inr h4 =>
    right
    linarith