import Mathlib

theorem algebra_10580 {a h k : ℝ} (ha : a ≠ 0) (h_eq : ∀ x, 2*x^2+6*x+11 = a*(x-h)^2+k) :
    h = -3/2 := by
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq (-1)
  have eq4 := h_eq 2
  have eq5 := h_eq (-2)
  nlinarith [sq_nonneg (a - 2), sq_nonneg (h + 3 / 2)]