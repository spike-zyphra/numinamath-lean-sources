import Mathlib

theorem inequalities_54391 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x ≥ z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) +
    y * (z + x) / (x * (x + y)) := by

  have h1 : 0 < x * y * z := by
    positivity

  have h2 : 0 < y * (y + z) := by
    positivity

  have h3 : 0 < z * (z + x) := by
    positivity

  have h4 : 0 < x * (x + y) := by
    positivity

  have h7 : x / y + y / z + z / x - (z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) + y * (z + x) / (x * (x + y))) ≥ 0 := by

    have h8 : x / y + y / z + z / x - (z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) + y * (z + x) / (x * (x + y))) =
        ((x - z) / (y + z) + (y - x) / (z + x) + (z - y) / (x + y)) := by
      field_simp
      ring
    rw [h8]

    have h11 : (x - z) / (y + z) + (y - x) / (z + x) + (z - y) / (x + y) ≥ 0 := by

      have h8 : (x - z) / (y + z) + (y - x) / (z + x) + (z - y) / (x + y) =
          ((x - z) * (z + x) * (x + y) + (y - x) * (y + z) * (x + y) + (z - y) * (y + z) * (z + x)) / ((y + z) * (z + x) * (x + y)) := by
        field_simp
        ring
      rw [h8]

      apply div_nonneg

      have h9 : (x - z) * (z + x) * (x + y) + (y - x) * (y + z) * (x + y) + (z - y) * (y + z) * (z + x) ≥ 0 := by
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
              mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
              mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz), 
              mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < z * x from mul_pos hz hx), 
              mul_pos (show 0 < y * z from mul_pos hy hz) (show 0 < z * x from mul_pos hz hx)]
      linarith [h9]

      positivity

    linarith [h11]

  linarith [h7]