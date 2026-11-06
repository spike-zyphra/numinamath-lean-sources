import Mathlib

theorem algebra_15981 {A B C : ℝ} (h : ∀ x, 4 * x / ((x - 5) * (x - 3) ^ 2) = A / (x - 5) + B / (x - 3) + C / (x - 3) ^ 2) :
    A = 5 ∧ B = -5 ∧ C = -6 := by

  have eq1 := h 6
  have eq2 := h 4
  have eq3 := h 2

  field_simp [(show (6 : ℝ) - 5 ≠ 0 by norm_num), (show (6 : ℝ) - 3 ≠ 0 by norm_num), 
          (show (6 - 3 : ℝ) ^ 2 ≠ 0 by norm_num), (show (4 : ℝ) - 5 ≠ 0 by norm_num), 
          (show (4 : ℝ) - 3 ≠ 0 by norm_num), (show (4 - 3 : ℝ) ^ 2 ≠ 0 by norm_num), 
          (show (2 : ℝ) - 5 ≠ 0 by norm_num), (show (2 : ℝ) - 3 ≠ 0 by norm_num), 
          (show (2 - 3 : ℝ) ^ 2 ≠ 0 by norm_num)] at eq1 eq2 eq3
  
  have h1 : A = 5 := by
    nlinarith
  
  have h2 : B = -5 := by 
    nlinarith
  
  have h3 : C = -6 := by 
    nlinarith
  
  exact ⟨h1, h2, h3⟩