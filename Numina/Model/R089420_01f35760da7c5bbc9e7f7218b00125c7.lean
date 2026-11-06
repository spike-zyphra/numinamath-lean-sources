import Mathlib

theorem algebra_19991 {a b c : ℤ} (h : a ≠ 0) (h1 : ∀ x, x^2 - 8 * x - 49 = (a * x + b)^2 + c) :
    a * b = -4 := by
  have eq1 := h1 0
  have eq2 := h1 1
  have eq3 := h1 (-1)
  ring_nf at eq1 eq2 eq3
  have eq4 : a^2 + 2 * (a * b) = -7 := by
    nlinarith [eq1, eq2]
  have eq5 : a^2 - 2 * (a * b) = 9 := by
    nlinarith [eq1, eq3]
  have eq6 : 4 * (a * b) = -16 := by
    nlinarith [eq4, eq5]
  have eq7 : a * b = -4 := by
    linarith
  exact eq7