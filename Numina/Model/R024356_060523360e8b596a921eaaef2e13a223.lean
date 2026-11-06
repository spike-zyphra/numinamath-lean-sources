import Mathlib

theorem algebra_20782 (x y : ℕ) (h : x * 5 = y * 3) (h' : x + y = 72) :
    x = 27 := by
  have eq1 : y = 72 - x := by
    omega
  rw [eq1] at h
  omega