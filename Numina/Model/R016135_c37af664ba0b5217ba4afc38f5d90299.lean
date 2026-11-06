import Mathlib

theorem inequalities_598720 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y / (z * (z + x)) + y * z / (x * (x + y)) + z * x / (y * (y + z)) ≥
    x / (z + x) + y / (x + y) + z / (y + z) := by

  have h1 : 0 < x * y * z * (x + y) * (y + z) * (z + x) := by
    positivity

  have h2 : x * y / (z * (z + x)) - x / (z + x) = x * (y - z) / (z * (z + x)) := by
    field_simp
    <;> ring_nf

  have h3 : y * z / (x * (x + y)) - y / (x + y) = y * (z - x) / (x * (x + y)) := by
    field_simp
    <;> ring_nf

  have h4 : z * x / (y * (y + z)) - z / (y + z) = z * (x - y) / (y * (y + z)) := by
    field_simp
    <;> ring_nf

  have h5 : x * (y - z) / (z * (z + x)) + y * (z - x) / (x * (x + y)) + z * (x - y) / (y * (y + z)) ≥ 0 := by
    have h6 : x * (y - z) / (z * (z + x)) + y * (z - x) / (x * (x + y)) + z * (x - y) / (y * (y + z)) =
      (x^2 * y * (y - z) * (x + y) * (y + z) + y^2 * z * (z - x) * (y + z) * (z + x) + z^2 * x * (x - y) * (x + y) * (z + x)) / (x * y * z * (x + y) * (y + z) * (z + x)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
              mul_pos (show 0 < x + y by linarith) (show 0 < y + z by linarith), 
              mul_pos (show 0 < x + y by linarith) (show 0 < z + x by linarith), 
              mul_pos (show 0 < y + z by linarith) (show 0 < z + x by linarith)
            ]
    all_goals
      positivity

  linarith [h2, h3, h4, h5]