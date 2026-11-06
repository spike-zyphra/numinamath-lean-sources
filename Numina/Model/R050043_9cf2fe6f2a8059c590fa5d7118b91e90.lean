import Mathlib

open Real

theorem algebra_321576 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (2 * x + y) + y / (x + 2 * y) ≤ 2 / 3 := by
  have h1 : 0 < 2 * x + y := by nlinarith
  have h2 : 0 < x + 2 * y := by nlinarith

  have h3 : x / (2 * x + y) + y / (x + 2 * y) - 2 / 3 ≤ 0 := by
    have h4 : x / (2 * x + y) + y / (x + 2 * y) - 2 / 3 =
      ( (x * (x + 2 * y) + y * (2 * x + y) - 2 / 3 * (2 * x + y) * (x + 2 * y)) ) / ( (2 * x + y) * (x + 2 * y) ) := by
      field_simp
      ring
    rw [h4]
    
    have h5 : (2 * x + y) * (x + 2 * y) > 0 := by positivity
    have h6 : x * (x + 2 * y) + y * (2 * x + y) - 2 / 3 * (2 * x + y) * (x + 2 * y) ≤ 0 := by
      nlinarith [sq_nonneg (x - y)]
    
    apply div_nonpos_of_nonpos_of_nonneg h6 (show 0 ≤ (2 * x + y) * (x + 2 * y) by positivity)
  
  linarith