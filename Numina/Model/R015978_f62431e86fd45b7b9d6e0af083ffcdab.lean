import Mathlib

theorem algebra_200018 {x : ℕ} (hx : x ≠ 0) (h : 340 - x * (1 - 1 / 4 : ℚ) = x) :
    x = 7 := by
  have h1 : (x : ℚ) ≠ 0 := by
    exact_mod_cast hx
  have eq1 : (x : ℚ) * (7 : ℚ) = (1360 : ℚ) := by
    nlinarith
  have eq2 : (x : ℤ) * 7 = 1360 := by
    exact_mod_cast eq1
  omega