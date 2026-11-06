import Mathlib

theorem inequalities_158348 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + 1) / (y + 1) + (y + 1) / (z + 1) + (z + 1) / (x + 1) ≤
    x / y + y / z + z / x := by
  have h1 : 0 < x * y * z := by
    positivity
  have hx1 : 0 < x + 1 := by
    linarith
  have hy1 : 0 < y + 1 := by
    linarith
  have hz1 : 0 < z + 1 := by
    linarith
  have h2 : (x / y + y / z + z / x) - ((x + 1) / (y + 1) + (y + 1) / (z + 1) + (z + 1) / (x + 1)) ≥ 0 := by
    have h3 : (x / y + y / z + z / x) - ((x + 1) / (y + 1) + (y + 1) / (z + 1) + (z + 1) / (x + 1)) =
          (x - y) / (y * (y + 1)) + (y - z) / (z * (z + 1)) + (z - x) / (x * (x + 1)) := by
      field_simp
      <;> ring
    rw [h3]
    have pos1 : 0 < y * (y + 1) := by
      positivity
    have pos2 : 0 < z * (z + 1) := by
      positivity
    have pos3 : 0 < x * (x + 1) := by
      positivity
    have h5 : (x - y) / (y * (y + 1)) + (y - z) / (z * (z + 1)) + (z - x) / (x * (x + 1)) =
        ((x - y) * (z * (z + 1)) * (x * (x + 1)) +
        (y - z) * (y * (y + 1)) * (x * (x + 1)) +
        (z - x) * (y * (y + 1)) * (z * (z + 1))
        ) / ((y * (y + 1)) * (z * (z + 1)) * (x * (x + 1))
        ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, mul_pos hx (show 0 < x + 1 by linarith),
        mul_pos hy (show 0 < y + 1 by linarith), mul_pos hz (show 0 < z + 1 by linarith)]
    positivity
  linarith