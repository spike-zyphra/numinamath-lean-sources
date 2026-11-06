import Mathlib

theorem algebra_153650 {A B C D : ℝ} (h : ∀ x : ℝ, x ≠ -1 → A / (x + 1) + B / (x + 1)^2 + (C * x + D) / (x^2 + x + 1) = 1 / ((x + 1)^2 * (x^2 + x + 1))) :
    A = 1 ∧ B = 1 ∧ C = -1 ∧ D = -1 := by
  have eq1 := h 0 (by norm_num)
  have eq2 := h 1 (by norm_num)
  have eq3 := h (-2) (by norm_num)
  have eq4 := h (-0.5) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4

  have hA : A = 1 := by
    linarith
  
  have hB : B = 1 := by 
    linarith
  
  have hC : C = -1 := by
    linarith

  have hD : D = -1 := by
    linarith
  
  exact ⟨hA, hB, hC, hD⟩