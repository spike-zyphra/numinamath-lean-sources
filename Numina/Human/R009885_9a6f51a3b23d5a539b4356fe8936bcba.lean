import Mathlib

/- The larger of two consecutive odd integers is three times the smaller.  What is their sum? -/
theorem algebra_14639 {n : ℕ} (hn : Odd n) (h : n + 2 = 3 * n) : n + (n + 2) = 4 := by
  omega