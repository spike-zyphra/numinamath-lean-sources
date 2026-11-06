import Mathlib

theorem algebra_1441 {A B C D : ℝ} (h : ∀ x, (4*x^3-6*x^2+6*x)/((x-1)^2*(x^2+1)) = A/(x-1) + B/(x-1)^2 + (C*x+D)/(x^2+1)) : A = 1 ∧ B = 2 ∧ C = 3 ∧ D = -1 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h (-1)
  norm_num at eq1 eq2 eq3 eq4 eq5
  exact ⟨by linarith, ⟨by linarith, ⟨by linarith, by linarith⟩ ⟩ ⟩