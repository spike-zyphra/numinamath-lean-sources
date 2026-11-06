import Mathlib

theorem inequalities_316994 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by

  have h1 : 0 < (2 * x + y + z) := by linarith only [hx, hy, hz];
  have h2 : 0 < (x + 2 * y + z) := by linarith only [hx, hy, hz];
  have h3 : 0 < (x + y + 2 * z) := by linarith only [hx, hy, hz];
  have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 := by
    have pos1 : 0 < ((2 * x + y + z)) := h1
    have pos2 : 0 < ((x + 2 * y + z)) := h2
    have pos3 : 0 < ((x + y + 2 * z)) := h3
    have pos4 : (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) > 0 := by positivity
    have h5 : (x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ) = 
          ((4 * x * (x + 2 * y + z) * (x + y + 2 * z) + 4 * y * (2 * x + y + z) * (x + y + 2 * z) + 4 * z * (2 * x + y + z) * (x + 2 * y + z) - 3 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) ) / (4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by 
      field_simp [h1, h2, h3]
      ring 
    rw [h5]
    have h6 : (4 * x * (x + 2 * y + z) * (x + y + 2 * z) + 4 * y * (2 * x + y + z) * (x + y + 2 * z) + 4 * z * (2 * x + y + z) * (x + 2 * y + z) - 3 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) ≤ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
        sq_nonneg (x * y - x * z), sq_nonneg (y * x - y * z), sq_nonneg (z * x - z * y), 
        mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3 ]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    positivity
  linarith