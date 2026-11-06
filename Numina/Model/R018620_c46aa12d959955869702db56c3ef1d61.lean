import Mathlib

theorem inequalities_308617 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 / ((2 * x + y) * (2 * x + z)) + y ^ 2 / ((2 * y + x) * (2 * y + z)) +
    z ^ 2 / ((2 * z + x) * (2 * z + y)) ≤ 1 / 3 := by

  have h1 : 0 < (2 * x + y) * (2 * x + z) := by positivity
  have h2 : 0 < (2 * y + x) * (2 * y + z) := by positivity
  have h3 : 0 < (2 * z + x) * (2 * z + y) := by positivity
  
  have h5 : (x ^ 2 * (2 * y + x) * (2 * y + z) * (2 * z + x) * (2 * z + y) * 3 +
      y ^ 2 * (2 * x + y) * (2 * x + z) * (2 * z + x) * (2 * z + y) * 3 +
      z ^ 2 * (2 * x + y) * (2 * x + z) * (2 * y + x) * (2 * y + z) * 3 ) ≤ ( (2 * x + y) * (2 * x + z) * (2 * y + x) * (2 * y + z) * (2 * z + x) * (2 * z + y) ) := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
        mul_pos (show 0 < 2 * x + y by nlinarith) (show 0 < 2 * x + z by nlinarith),
        mul_pos (show 0 < 2 * y + x by nlinarith) (show 0 < 2 * y + z by nlinarith),
        mul_pos (show 0 < 2 * z + x by nlinarith) (show 0 < 2 * z + y by nlinarith)
      ]

  have h6 : (x ^ 2 / ((2 * x + y) * (2 * x + z)) + y ^ 2 / ((2 * y + x) * (2 * y + z)) + z ^ 2 / ((2 * z + x) * (2 * z + y)) - 1 / 3) = (x ^ 2 * (2 * y + x) * (2 * y + z) * (2 * z + x) * (2 * z + y) * 3 + y ^ 2 * (2 * x + y) * (2 * x + z) * (2 * z + x) * (2 * z + y) * 3 + z ^ 2 * (2 * x + y) * (2 * x + z) * (2 * y + x) * (2 * y + z) * 3 - ( (2 * x + y) * (2 * x + z) * (2 * y + x) * (2 * y + z) * (2 * z + x) * (2 * z + y) ) ) / (3 * ( (2 * x + y) * (2 * x + z) * (2 * y + x) * (2 * y + z) * (2 * z + x) * (2 * z + y) )) := by
    field_simp
    <;> ring

  have h7 : (x ^ 2 / ((2 * x + y) * (2 * x + z)) + y ^ 2 / ((2 * y + x) * (2 * y + z)) + z ^ 2 / ((2 * z + x) * (2 * z + y)) - 1 / 3) ≤ 0 := by 
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    positivity

  linarith