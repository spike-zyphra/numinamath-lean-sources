import Mathlib

theorem algebra_287016 (x : ℕ) (hx : x > 0) (h : 25 * 3 = 25 * x + x * 25) :
    IsLeast {y | y > 0 ∧ 25 * 3 = 25 * y + y * 25 ∧ y * 1595 > 1595} 29 := by
  omega