import Mathlib

theorem inequalities_102576 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hzz : x * y * z = 1) :
    3 ≤ (1 + x * y) / (1 + z) + (1 + y * z) / (1 + x) + (1 + x * z) / (1 + y) := by

  have h1 : 0 < x * y * z := by
    positivity

  have h2 : 0 < (1 + z) * (1 + x) * (1 + y) := by
    positivity

  have h3 : (1 + x * y) / (1 + z) + (1 + y * z) / (1 + x) + (1 + x * z) / (1 + y) - 3 ≥ 0 := by
    have h4 : (1 + x * y) / (1 + z) + (1 + y * z) / (1 + x) + (1 + x * z) / (1 + y) - 3 =
        ((1 + x * y) * (1 + x) * (1 + y) + (1 + y * z) * (1 + z) * (1 + y) + (1 + x * z) * (1 + z) * (1 + x) - 3 * (1 + z) * (1 + x) * (1 + y)) / ((1 + z) * (1 + x) * (1 + y)) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (x * z - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hzz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    all_goals positivity

  linarith