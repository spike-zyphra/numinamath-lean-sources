import Mathlib

theorem algebra_12776 (A B C D E : ℝ) (h : ∀ x, 1/(x*(x+1)*(x+2)*(x+3)*(x+4)) = A/x + B/(x+1) + C/(x+2) + D/(x+3) + E/(x+4)) :
    A + B + C + D + E = 0 := by
  have eq1 := h 1
  have eq2 := h 2
  have eq3 := h 3
  have eq4 := h 4
  have eq5 := h 5
  norm_num at eq1 eq2 eq3 eq4 eq5
  linarith