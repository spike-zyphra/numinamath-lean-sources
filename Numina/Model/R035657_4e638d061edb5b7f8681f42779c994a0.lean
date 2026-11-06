import Mathlib

theorem inequalities_126655 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) +
    z / (z + 2 * x + 3 * y) ≥ 1 / 2 := by

  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 0 < (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) := by
    positivity
  
  have h3 : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) - 1 / 2 ≥ 0 := by 
    have h4 : 0 < (x + 2 * y + 3 * z) := by positivity
    have h5 : 0 < (y + 2 * z + 3 * x) := by positivity
    have h6 : 0 < (z + 2 * x + 3 * y) := by positivity
    have h7 : 0 < (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) := by positivity
    have h3' : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) - 1 / 2 =
          (2 * (x * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) + y * (x + 2 * y + 3 * z) * (z + 2 * x + 3 * y) + z * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x)) - (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y)) / (2 * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y)) := by
      field_simp
      ring
    rw [h3']
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos hx hz, mul_pos hy hz, mul_pos hz hx, mul_pos (mul_pos hx hy) hz, mul_pos (mul_pos hx hz) hy]
    all_goals positivity
  
  linarith