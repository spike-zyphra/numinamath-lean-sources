import Mathlib

theorem algebra_324441 (a b c : ℝ) (hb : b ≠ 0)
    (x1 x2 y1 y2 : ℝ)
    (h1 : x1^2 + a * x2^2 = b)
    (h2 : x2 * y1 - x1 * y2 = a)
    (h3 : x1 * y1 + a * x2 * y2 = c) :
    y1^2 + a * y2^2 = (c^2 + a^3) / b := by
  have eq1 : (x1 ^ 2 + a * x2 ^ 2) * (y1 ^ 2 + a * y2 ^ 2) = (x1 * y1 + a * x2 * y2) ^ 2 + a * (x2 * y1 - x1 * y2) ^ 2 := by
    ring
  rw [h1, h2, h3] at eq1
  have eq2 : b * (y1 ^ 2 + a * y2 ^ 2) = c ^ 2 + a ^ 3 := by
    nlinarith
  have eq3 : y1 ^ 2 + a * y2 ^ 2 = (c ^ 2 + a ^ 3) / b := by
    field_simp [hb]
    linarith
  exact eq3