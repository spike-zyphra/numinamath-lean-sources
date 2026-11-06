import Mathlib

theorem algebra_22253 {A B C : ℝ} (h : ∀ x, x ≠ 0 ∧ x ≠ -1 ∧ x ≠ -3 → (x + 2) / (x * (x + 1) * (x + 3)) = A / x + B / (x + 1) + C / (x + 3)) : A * B * C = 1 / 18 := by
  have eq1 := h 1 (by norm_num)
  have eq2 := h (-2) (by norm_num)
  have eq3 := h 2 (by norm_num)
  norm_num at eq1 eq2 eq3 
  have eq4 : A = 2 / 3 := by
    linarith
  have eq5 : B = -1 / 2 := by
    rw [eq4] at eq1 eq2
    linarith 
  have eq6 : C = -1 / 6 := by
    rw [eq4, eq5] at eq1 eq2
    linarith 
  rw [eq4, eq5, eq6]
  norm_num