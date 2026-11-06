import Mathlib

theorem inequalities_603304 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by
  have h1 : 2 * x + y + z > 0 := by
    nlinarith
  have h2 : x + 2 * y + z > 0 := by
    nlinarith
  have h3 : x + y + 2 * z > 0 := by
    nlinarith
  suffices x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 by linarith
  have pos1 : (2 * x + y + z) > 0 := by 
    nlinarith
  have pos2 : (x + 2 * y + z) > 0 := by 
    nlinarith
  have pos3 : (x + y + 2 * z) > 0 := by 
    nlinarith
  have eq : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 =
      (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z) - 3 / 4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
    field_simp
    ring
  rw [eq]
  apply div_nonpos_of_nonpos_of_nonneg
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
  positivity