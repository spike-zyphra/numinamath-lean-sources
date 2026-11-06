import Mathlib

theorem algebra_94140 (n k : ℤ) (h : k + n * 10 + 4 * (50 - n) > (k - 50) + 50 * 10) 
: n ≥ 42 := by
  linarith