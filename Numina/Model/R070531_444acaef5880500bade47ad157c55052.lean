import Mathlib

theorem algebra_5066 {x : ℝ} (hxpos : 0 < x) (hx : x + 1/x = 3) :
    x^3 + 1/x^3 = 18 := by 
  have h1 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by 
    field_simp
    ring
  rw [h1, hx]
  norm_num