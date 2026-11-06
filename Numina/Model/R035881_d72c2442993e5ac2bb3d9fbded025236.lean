import Mathlib

theorem inequalities_608100 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) +
    (z - x) / (z * x + 2 * x + 1) ≥ 0 := by
  have h1 : x * y + 2 * y + 1 > 0 := by
    nlinarith [hy, hx]
  have h2 : y * z + 2 * z + 1 > 0 := by
    nlinarith [hz, hy]
  have h3 : z * x + 2 * x + 1 > 0 := by
    nlinarith [hz, hx]
  have h5 : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) +
          (z - x) / (z * x + 2 * x + 1) = 
          ((x - y) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1) + 
          (y - z) * (x * y + 2 * y + 1) * (z * x + 2 * x + 1) + 
          (z - x) * (x * y + 2 * y + 1) * (y * z + 2 * z + 1)) / ((x * y + 2 * y + 1) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1)) := by
    field_simp [h1, h2, h3]
    <;> ring
  rw [h5]
  apply div_nonneg
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg ((x * y) - (y * z)), sq_nonneg ((y * z) - (z * x)), sq_nonneg ((z * x) - (x * y)),
          mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx]
  positivity