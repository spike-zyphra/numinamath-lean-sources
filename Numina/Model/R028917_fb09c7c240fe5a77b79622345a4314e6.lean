import Mathlib

theorem algebra_318853 {A B : ℝ} (h : ∀ x, x ≠ 2 → x ≠ -1 → (3 * x + 4) / (x ^ 2 - x - 2) = A / (x - 2) - B / (x + 1)) :
    4 * A - B = 13 := by

  have eq1 := h 0 (by norm_num) (by norm_num)
  have eq2 := h 1 (by norm_num) (by norm_num)
  norm_num at eq1 eq2
  have eq3 : A + 2 * B = 4 := by
    linarith
  have eq4 : 2 * A + B = 7 := by
    linarith
  have hA : A = 10 / 3 := by
    linarith [eq3, eq4]
  have hB : B = 1 / 3 := by
    linarith [eq3, eq4]
  rw [hA, hB]
  norm_num