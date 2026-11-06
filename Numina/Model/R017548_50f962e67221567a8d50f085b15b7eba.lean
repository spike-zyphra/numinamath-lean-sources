import Mathlib

theorem inequalities_45714 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z ≤ 1) :
    ((1 / x - 1) * (1 / y - 1) * (1 / z - 1)) ≥ 8 := by
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h2 : (1 / x - 1) * (1 / y - 1) * (1 / z - 1) - 8 ≥ 0 := by
    have h3 : (1 / x - 1) * (1 / y - 1) * (1 / z - 1) - 8 =
        ((1 - x) * (1 - y) * (1 - z) - 8 * (x * y * z)) / (x * y * z) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h3]
    have h4 : (1 - x) * (1 - y) * (1 - z) ≥ 8 * (x * y * z) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 1), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
        mul_nonneg (show (0 : ℝ) ≤ 1 - (x + y + z) by nlinarith) (show (0 : ℝ) ≤ x by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ 1 - (x + y + z) by nlinarith) (show (0 : ℝ) ≤ y by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ 1 - (x + y + z) by nlinarith) (show (0 : ℝ) ≤ z by nlinarith)]
    have h5 : ( (1 - x) * (1 - y) * (1 - z) - 8 * (x * y * z) ) ≥ 0 := by
      nlinarith [h4]
    have h6 : ((1 - x) * (1 - y) * (1 - z) - 8 * (x * y * z)) / (x * y * z) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith