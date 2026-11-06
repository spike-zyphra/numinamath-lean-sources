import Mathlib

theorem algebra_219912 {x : ℕ} (hx : x ≠ 0) (h1 : (1 / 3 : ℚ) * x + (1 / 5 : ℚ) * x + (1 / 6 : ℚ) * x + (1 / 4 : ℚ) * x + 6 = x) :
    x = 120 := by

  have eq1 : (x : ℚ) = 120 := by
    linarith
  exact_mod_cast eq1