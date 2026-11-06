import Mathlib

theorem algebra_165363 (x : ℕ) (hx : x ≠ 0) (h : (1 / 3 : ℚ) * x + (1 / 5 : ℚ) * x = (1 / 2 : ℚ) * x + 7) :
    x = 210 := by
  have eq1 : (x : ℚ) = 210 := by
    linarith
  exact_mod_cast eq1