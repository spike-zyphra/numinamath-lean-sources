import Mathlib

theorem inequalities_598167 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by 
  have h1 : 0 < x + y := by nlinarith
  have h2 : 0 < y + z := by nlinarith
  have h3 : 0 < z + x := by nlinarith
  have h4 : 0 < (x + y) * (y + z) * (z + x) := by positivity
  suffices 5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) by linarith
  have h5 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by 
    have h6 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 =
        (( (y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z) ) - (5 / 2) * (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x)) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (x + y + z - 2), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - 1 / 4), sq_nonneg (y * z - 1 / 4), sq_nonneg (z * x - 1 / 4),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h]
    positivity
  linarith