import Mathlib

theorem algebra_165108 {a b : ℝ} (h : ∀ x y, (x + y - 2) ∣ (x ^ 2 + a * x * y + b * y ^ 2 - 5 * x + y + 6)) :
    a - b = 1 := by
  have eq1 := h 1 1
  norm_num at eq1
  have eq4 := h 0 2
  norm_num at eq4
  have eq6 : a + b = -3 := by
    linarith
  have eq7 : 4 * b + 8 = 0 := by
    linarith
  have eq8 : b = -2 := by
    linarith
  have eq9 : a = -1 := by
    linarith [eq6, eq8]
  linarith [eq9, eq8]