import Mathlib

theorem inequalities_598874 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * z / (x^2 + x * z + y * z) + x * y / (y^2 + x * y + x * z) +
    y * z / (z^2 + y * z + x * y) ≤ 1 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < y * z := mul_pos hy hz
  have h3 : 0 < z * x := mul_pos hz hx
  have D1_pos : 0 < x^2 + x * z + y * z := by positivity
  have D2_pos : 0 < y^2 + x * y + x * z := by positivity
  have D3_pos : 0 < z^2 + y * z + x * y := by positivity
  have h4 : x * z / (x^2 + x * z + y * z) + x * y / (y^2 + x * y + x * z) + y * z / (z^2 + y * z + x * y) - 1 ≤ 0 := by
    have h5 : x * z / (x^2 + x * z + y * z) + x * y / (y^2 + x * y + x * z) + y * z / (z^2 + y * z + x * y) - 1 =
        (x * z * (y^2 + x * y + x * z) * (z^2 + y * z + x * y) + 
         x * y * (x^2 + x * z + y * z) * (z^2 + y * z + x * y) + 
         y * z * (x^2 + x * z + y * z) * (y^2 + x * y + x * z) - 
         (x^2 + x * z + y * z) * (y^2 + x * y + x * z) * (z^2 + y * z + x * y)) / 
        ((x^2 + x * z + y * z) * (y^2 + x * y + x * z) * (z^2 + y * z + x * y)) := by
      field_simp
      ring
    rw [h5]
    have h6 : (x^2 + x * z + y * z) * (y^2 + x * y + x * z) * (z^2 + y * z + x * y) > 0 := by positivity
    have h7 : x * z * (y^2 + x * y + x * z) * (z^2 + y * z + x * y) + 
         x * y * (x^2 + x * z + y * z) * (z^2 + y * z + x * y) + 
         y * z * (x^2 + x * z + y * z) * (y^2 + x * y + x * z) - 
         (x^2 + x * z + y * z) * (y^2 + x * y + x * z) * (z^2 + y * z + x * y) ≤ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (x * z - x * y), sq_nonneg (x * z - y * z), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
    apply div_nonpos_of_nonpos_of_nonneg h7 (by positivity)
  linarith