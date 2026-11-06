import Mathlib

theorem inequalities_597978 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (k1 k2 : ℝ) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) (k : ℝ) (hk : k = k1 + k2) :
    0 ≤ (k * y^2 - k1 * z^2 - k2 * x^2) / (z + x) + (k * z^2 - k1 * x^2 - k2 * y^2) / (x + y) +
        (k * x^2 - k1 * y^2 - k2 * z^2) / (y + z) := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < y * z := mul_pos hy hz
  have h3 : 0 < z * x := mul_pos hz hx
  have h4 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  have h5 : 0 < z + x := by linarith
  have h6 : 0 < x + y := by linarith
  have h7 : 0 < y + z := by linarith
  have hk3 : k = k1 + k2 := hk
  have h12 : (k * y^2 - k1 * z^2 - k2 * x^2) / (z + x) + (k * z^2 - k1 * x^2 - k2 * y^2) / (x + y) + (k * x^2 - k1 * y^2 - k2 * z^2) / (y + z) =
      (((k1 + k2) * y^2 - k1 * z^2 - k2 * x^2) * (x + y) * (y + z) + ((k1 + k2) * z^2 - k1 * x^2 - k2 * y^2) * (z + x) * (y + z) + ((k1 + k2) * x^2 - k1 * y^2 - k2 * z^2) * (z + x) * (x + y)) / ((z + x) * (x + y) * (y + z)) := by
    rw [hk3]
    field_simp
    <;> ring
  rw [h12]
  have h13 : ((k1 + k2) * y^2 - k1 * z^2 - k2 * x^2) * (x + y) * (y + z) + ((k1 + k2) * z^2 - k1 * x^2 - k2 * y^2) * (z + x) * (y + z) + ((k1 + k2) * x^2 - k1 * y^2 - k2 * z^2) * (z + x) * (x + y) ≥ 0 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
      mul_nonneg hk1 hk2, mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ z by linarith), 
      mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
      mul_nonneg hk1 (show 0 ≤ x by linarith), mul_nonneg hk1 (show 0 ≤ y by linarith), 
      mul_nonneg hk1 (show 0 ≤ z by linarith), 
      mul_nonneg hk2 (show 0 ≤ x by linarith), 
      mul_nonneg hk2 (show 0 ≤ y by linarith), 
      mul_nonneg hk2 (show 0 ≤ z by linarith)]
  apply div_nonneg
  linarith
  all_goals
    positivity