import Mathlib

theorem algebra_174528 (x : ℕ) (hx : x > 0) (h : x + (x + 5) + (x + 10) + (x + 15) = 25 * x) :
    x = 25 := by
  omega