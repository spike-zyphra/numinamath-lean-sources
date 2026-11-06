import Mathlib

theorem inequalities_129007 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 3) :
    (x^2 + y * z) / (x^2 + y * z + 1) +
    (y^2 + z * x) / (y^2 + z * x + 1) +
    (z^2 + x * y) / (z^2 + x * y + 1) ≤ 2 := by
  have h1 : 0 < (x^2 + y * z + 1) := by positivity
  have h2 : 0 < (y^2 + z * x + 1) := by positivity
  have h3 : 0 < (z^2 + x * y + 1) := by positivity

  have h4 : (x^2 + y * z) / (x^2 + y * z + 1) +
      (y^2 + z * x) / (y^2 + z * x + 1) +
      (z^2 + x * y) / (z^2 + x * y + 1) ≤ 2 := by
    have h5 : (x^2 + y * z) / (x^2 + y * z + 1) +
        (y^2 + z * x) / (y^2 + z * x + 1) +
        (z^2 + x * y) / (z^2 + x * y + 1) - 2 ≤ 0 := by 
      have h6 : (x^2 + y * z) / (x^2 + y * z + 1) +
          (y^2 + z * x) / (y^2 + z * x + 1) +
          (z^2 + x * y) / (z^2 + x * y + 1) - 2 =
              ( (x^2 + y * z) * (y^2 + z * x + 1) * (z^2 + x * y + 1) + (y^2 + z * x) * (x^2 + y * z + 1) * (z^2 + x * y + 1) + (z^2 + x * y) * (x^2 + y * z + 1) * (y^2 + z * x + 1) - 2 * (x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1) ) / ( (x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1) ) := by
        field_simp
        ring
      rw [h6] 
      apply div_nonpos_of_nonpos_of_nonneg 
      -- The goal here is to show the numerator is nonpositive.
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        sq_nonneg (x^2 + y^2 + z^2 - 3), 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
        mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
      ]
      positivity
    linarith
  linarith