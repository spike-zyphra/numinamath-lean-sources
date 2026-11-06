import Mathlib

theorem algebra_244204 (x y : ℕ) (hxy : x + y = 280) (hxy1 : x * 2 = y * 5) (hxy2 : x * 60 / 100 + y * 2 = 1360) :
    x * 2 + y * 5 = 640 := by
  omega