import Mathlib

theorem algebra_312309 (a b : Fin 4 → ℝ)
    (h : ∀ x, x^4 + a 0 * x^3 + a 1 * x^2 + a 2 * x + a 3 =
      (x + 1)^4 + b 0 * (x + 1)^3 + b 1 * (x + 1)^2 + b 2 * (x + 1) + b 3) :
    b 2 = -4 + 3 * a 0 - 2 * a 1 + a 2 := by
  have eq1 := h 0
  norm_num at eq1
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  norm_num at eq2 eq3 eq4 eq5
  ring_nf at eq1 eq2 eq3 eq4 eq5 ⊢
  linarith