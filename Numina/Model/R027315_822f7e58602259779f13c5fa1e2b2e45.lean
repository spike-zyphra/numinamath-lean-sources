import Mathlib

theorem inequalities_302900 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) +
        (z - x) / (z * x + 2 * x + 1) := by
  have h1 : 0 < x * y + 2 * y + 1 := by
    nlinarith 
  have h2 : 0 < y * z + 2 * z + 1 := by
    nlinarith 
  have h3 : 0 < z * x + 2 * x + 1 := by
    nlinarith 
  have h4 : 0 ≤ (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) := by
    have h5 : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) =
        ((x - y) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1) + (y - z) * (x * y + 2 * y + 1) * (z * x + 2 * x + 1) + (z - x) * (x * y + 2 * y + 1) * (y * z + 2 * z + 1)) / ((x * y + 2 * y + 1) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1)) := by
      field_simp
      <;> ring 
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, 
      mul_nonneg (show 0 ≤ x * y from by nlinarith) (show 0 ≤ y * z from by nlinarith), 
      mul_nonneg (show 0 ≤ y * z from by nlinarith) (show 0 ≤ z * x from by nlinarith), 
      mul_nonneg (show 0 ≤ z * x from by nlinarith) (show 0 ≤ x * y from by nlinarith)]
    positivity 
  linarith