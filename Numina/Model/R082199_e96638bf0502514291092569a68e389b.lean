import Mathlib

theorem inequalities_319154 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by 
  have h1 : 0 < 2 * x + y + z := by nlinarith
  have h2 : 0 < x + 2 * y + z := by nlinarith
  have h3 : 0 < x + y + 2 * z := by nlinarith
  
  have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 := by
    have h5 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 =
          ( (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z) - 3 / 4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) ) := by 
      field_simp
      <;> ring 
    rw [h5]
    have h6 : (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) > 0 := by positivity
    have h7 : (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z) - 3 / 4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) ≤ 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - (x + y + z) / 4), sq_nonneg (y - (x + y + z) / 4), sq_nonneg (z - (x + y + z) / 4),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    apply div_nonpos_of_nonpos_of_nonneg h7 (show (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) ≥ 0 by positivity)
  
  linarith