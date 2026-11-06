import Mathlib

theorem algebra_19287 {A B : ℝ} (h : ∀ x, x ≠ 3 → x ≠ 5 → 4 * x / (x ^ 2 - 8 * x + 15) = A / (x - 3) + B / (x - 5)) :
    A = -6 ∧ B = 10 := by
  have eq1 := h 0 (by norm_num) (by norm_num)
  have eq2 := h 1 (by norm_num) (by norm_num)
  have eq3 := h 2 (by norm_num) (by norm_num)
  have eq4 := h 6 (by norm_num) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4
  constructor
  · -- Solving the system of equations to find A and B
    linarith
  · -- Solving the system of equations to find A and B
    linarith