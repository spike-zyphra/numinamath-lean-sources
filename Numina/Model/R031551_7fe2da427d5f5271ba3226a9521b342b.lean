import Mathlib

theorem inequalities_1894 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x + x * y * z = 4) :
    1 ≤ y * z / (2 + x) + z * x / (2 + y) + x * y / (2 + z) := by
  have h1 : 0 < (2 + x) * (2 + y) * (2 + z) := by
    positivity
  have eq1 : y * z / (2 + x) + z * x / (2 + y) + x * y / (2 + z) - 1 ≥ 0 := by
    have h2 : 0 < (2 + x) := by linarith
    have h3 : 0 < (2 + y) := by linarith
    have h4 : 0 < (2 + z) := by linarith
    have h5 : y * z / (2 + x) + z * x / (2 + y) + x * y / (2 + z) - 1 =
        ( (y * z * (2 + y) * (2 + z) + z * x * (2 + x) * (2 + z) + x * y * (2 + x) * (2 + y) - (2 + x) * (2 + y) * (2 + z)) / ((2 + x) * (2 + y) * (2 + z)) ) := by 
      field_simp
      ring 
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y * z - 1), sq_nonneg (x * y + y * z + z * x - 3),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h]
    positivity
  linarith