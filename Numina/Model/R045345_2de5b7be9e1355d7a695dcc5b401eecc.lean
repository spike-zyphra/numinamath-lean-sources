import Mathlib

theorem algebra_239297 {a b c : ℝ} (h : 7 * a^2 = 7 * b^2 + 3 * c^2) :
    (5 * a - 2 * b + 3 * c) * (5 * a - 2 * b - 3 * c) = (2 * a - 5 * b)^2 := by
  have hc : 3 * c^2 = 7 * a^2 - 7 * b^2 := by
    nlinarith
  calc
    (5 * a - 2 * b + 3 * c) * (5 * a - 2 * b - 3 * c)
        = (5 * a - 2 * b)^2 - (3 * c)^2 := by ring
    _ = 25 * a^2 - 20 * a * b + 4 * b^2 - 9 * c^2 := by
      ring
    _ = 4 * a^2 - 20 * a * b + 25 * b^2 := by
      have hc3 : 9 * c^2 = 21 * a^2 - 21 * b^2 := by
        nlinarith [hc]
      nlinarith [hc3]
    _ = (2 * a - 5 * b)^2 := by
      ring