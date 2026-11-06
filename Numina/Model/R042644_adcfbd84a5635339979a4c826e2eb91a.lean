import Mathlib

theorem algebra_130254 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    2 ≤ (x + y) * (y + z) := by

  have h1 : 0 < (x + y) * (y + z) := by
    positivity

  have h2 : (x + y) * (y + z) = y * (x + y + z) + x * z := by
    ring

  have h3 : y * (x + y + z) > 0 := by
    positivity

  have h4 : x * z = 1 / (y * (x + y + z)) := by
    field_simp [(show y * (x + y + z) ≠ 0 by positivity)]
    nlinarith [h]

  have h9 : y * (x + y + z) + x * z ≥ 2 := by
    have h11 : (y * (x + y + z)) * (x * z) = 1 := by
      nlinarith [h, h4]
    nlinarith [sq_nonneg (y * (x + y + z) - 1), sq_nonneg (x * z - 1),
      mul_pos h3 (show 0 < (x * z : ℝ) by positivity)]

  nlinarith [h2, h9]