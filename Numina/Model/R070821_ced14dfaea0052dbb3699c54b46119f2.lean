import Mathlib

theorem algebra_95016 {N1 N2 : ℝ} (h : ∀ x, x^2 - 3 * x + 2 ≠ 0 → (35 * x - 29) / (x^2 - 3 * x + 2) = N1 / (x - 1) + N2 / (x - 2)) :
    N1 * N2 = -246 := by
  have eq1 := h 0 (by norm_num)
  have eq2 := h 3 (by norm_num)
  have eq3 := h 4 (by norm_num)
  norm_num at eq1 eq2 eq3
  have h1 : N1 = -6 := by
    linarith [eq1, eq2, eq3]
  have h2 : N2 = 41 := by
    linarith [eq1, eq2, eq3]
  rw [h1, h2]
  norm_num