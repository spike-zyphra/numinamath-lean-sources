import Mathlib

open Real

theorem algebra_153523 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (2 * x + y) + y / (x + 2 * y) ≤ 2 / 3 := by 
  have h1 : 0 < 2 * x + y := by
    nlinarith
  have h2 : 0 < x + 2 * y := by
    nlinarith
  have h3 : 0 < 3 * (2 * x + y) * (x + 2 * y) := by 
    positivity
  have h4 : x / (2 * x + y) + y / (x + 2 * y) - (2 / 3) ≤ 0 := by 
    have h5 : (x / (2 * x + y) + y / (x + 2 * y) - (2 / 3)) =
        (3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y)) / (3 * (2 * x + y) * (x + 2 * y)) := by 
      field_simp
      ring
    rw [h5]
    have h6 : (3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y)) ≤ 0 := by 
      nlinarith [sq_nonneg (x - y)]
    apply div_nonpos_of_nonpos_of_nonneg h6 (by positivity)
  linarith