import Mathlib

theorem inequalities_7002 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y / ((3 * x + z) * (3 * y + z)) + y * z / ((3 * y + x) * (3 * z + x)) +
    z * x / ((3 * z + y) * (3 * x + y)) ≤ 3 / 16 := by
  have hx1 : 0 < 3 * x + z := by nlinarith
  have hy1 : 0 < 3 * y + z := by nlinarith
  have hx2 : 0 < 3 * y + x := by nlinarith
  have hy2 : 0 < 3 * z + x := by nlinarith
  have hx3 : 0 < 3 * z + y := by nlinarith
  have hy3 : 0 < 3 * x + y := by nlinarith
  have h1 : 0 < (3 * x + z) * (3 * y + z) * (3 * y + x) * (3 * z + x) * (3 * z + y) * (3 * x + y) := by positivity
  have h2 : x * y / ((3 * x + z) * (3 * y + z)) + y * z / ((3 * y + x) * (3 * z + x)) + z * x / ((3 * z + y) * (3 * x + y)) - 3 / 16 ≤ 0 := by
    have hx1 : 0 < (3 * x + z) := by nlinarith
    have hy1 : 0 < (3 * y + z) := by nlinarith
    have hx2 : 0 < (3 * y + x) := by nlinarith
    have hy2 : 0 < (3 * z + x) := by nlinarith
    have hx3 : 0 < (3 * z + y) := by nlinarith
    have hy3 : 0 < (3 * x + y) := by nlinarith
    have h1 : 0 < (3 * x + z) * (3 * y + z) * (3 * y + x) * (3 * z + x) * (3 * z + y) * (3 * x + y) := by positivity
    have h3 : (x * y / ((3 * x + z) * (3 * y + z)) + y * z / ((3 * y + x) * (3 * z + x)) + z * x / ((3 * z + y) * (3 * x + y)) - 3 / 16) ≤ 0 := by
      have h4 : x * y / ((3 * x + z) * (3 * y + z)) + y * z / ((3 * y + x) * (3 * z + x)) + z * x / ((3 * z + y) * (3 * x + y)) - 3 / 16 =
          (x * y * (3 * y + x) * (3 * z + x) * (3 * z + y) * (3 * x + y) + 
          y * z * (3 * x + z) * (3 * y + z) * (3 * z + y) * (3 * x + y) + 
          z * x * (3 * x + z) * (3 * y + z) * (3 * y + x) * (3 * z + x) - 
          3 / 16 * (3 * x + z) * (3 * y + z) * (3 * y + x) * (3 * z + x) * (3 * z + y) * (3 * x + y)) / ((3 * x + z) * (3 * y + z) * (3 * y + x) * (3 * z + x) * (3 * z + y) * (3 * x + y)) := by 
          field_simp
          ring 
      rw [h4]
      apply div_nonpos_of_nonpos_of_nonneg
      -- Show the numerator is non-positive
      · nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]
      -- Show the denominator is non-negative
      · positivity
    linarith 
  linarith