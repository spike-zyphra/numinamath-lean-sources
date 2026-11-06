import Mathlib

theorem inequalities_300240 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    (z - y) / (x + 2 * y) + (x - z) / (y + 2 * z) + (y - x) / (z + 2 * x) ≥ 0 := by
  have h1 : 0 < x + 2 * y := by nlinarith
  have h2 : 0 < y + 2 * z := by nlinarith
  have h3 : 0 < z + 2 * x := by nlinarith
  have h4 : (z - y) / (x + 2 * y) + (x - z) / (y + 2 * z) + (y - x) / (z + 2 * x) =
    ((z - y) * (y + 2 * z) * (z + 2 * x) + (x - z) * (x + 2 * y) * (z + 2 * x) + (y - x) * (x + 2 * y) * (y + 2 * z)) / ((x + 2 * y) * (y + 2 * z) * (z + 2 * x)) := by
    field_simp [h1, h2, h3]
    ring_nf
    <;> field_simp [h1, h2, h3]
    <;> ring
  have h5 : 0 ≤ (z - y) * (y + 2 * z) * (z + 2 * x) + (x - z) * (x + 2 * y) * (z + 2 * x) + (y - x) * (x + 2 * y) * (y + 2 * z) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
        sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z),
        hsum]
  rw [h4]
  apply div_nonneg
  linarith
  positivity
  all_goals nlinarith