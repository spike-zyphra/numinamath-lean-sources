import Mathlib

theorem algebra_266779 (a b c x y z : ℝ) (ha : a < b) (hb : b < c) (hx : x < y) (hy : y < z) :
    max (max (max (a * x + b * y + c * z) (a * x + b * z + c * y)) (b * x + a * y + c * z)) (b * x + c * y + a * z) = a * x + b * y + c * z := by
  have h1 : a * x + b * y + c * z ≥ a * x + b * z + c * y := by 
    nlinarith
  have h2 : a * x + b * y + c * z ≥ b * x + a * y + c * z := by
    nlinarith
  have h3 : a * x + b * y + c * z ≥ b * x + c * y + a * z := by
    nlinarith
  simp [max_eq_left_of_lt, h1, h2, h3]
  all_goals linarith