import Mathlib

theorem algebra_273019 (x y z : ℝ) (h : z^3 = x^3 + y^3) (h₁ : x + y ≠ 0) (h₂ : z - x ≠ 0) (h₃ : z - y ≠ 0) :
    (x + y - z)^3 / ((x + y) * (z - x) * (z - y)) = 3 := by 
  have eq1 : z^3 - x^3 - y^3 = 0 := by linarith 
  have eq2 : (x + y - z) ^ 3 = 3 * ((x + y) * (z - x) * (z - y)) := by 
    nlinarith [sq_pos_of_ne_zero (show (x + y) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z - x) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z - y) ≠ 0 by assumption), sq_nonneg (x - y), sq_nonneg (z - x - y), sq_nonneg (x + y - z)]
  have eq3 : (x + y - z) ^ 3 / ((x + y) * (z - x) * (z - y)) = 3 := by 
    have h4 : (x + y) * (z - x) * (z - y) ≠ 0 := by 
      apply mul_ne_zero 
      apply mul_ne_zero 
      exact h₁ 
      exact h₂
      exact h₃ 
    field_simp [h4] 
    linarith [eq2]
  exact eq3