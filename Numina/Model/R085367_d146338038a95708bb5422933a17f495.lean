import Mathlib

theorem algebra_197182 {x y : ℕ} (hxy : x < y) (h : x * 15 + y * 20 = 150) (h' : x * 20 + y * 15 = 75) :
    x = 6 ∧ y = 2 := by
  omega