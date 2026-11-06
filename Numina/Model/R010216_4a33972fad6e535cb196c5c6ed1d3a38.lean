import Mathlib

theorem algebra_10922 {x y : ℕ} (xpos : 0 < x) (ypos : 0 < y) (hx : x < 20) (hy : y < 20)
 (h : x + y + x * y = 76) : x + y = 16 := by
  interval_cases x <;> interval_cases y <;> omega