import Mathlib

theorem algebra_10878 {a b c : ℤ} (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 + b * x + c = x ^ 2 + 2 * x - 1) :
    a = 1 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1)
  have eq4 : c = -1 := by
    omega
  have eq5 : a + b = 3 := by
    rw [eq4] at eq2
    omega
  have eq6 : a - b = -1 := by
    rw [eq4] at eq3
    omega
  omega