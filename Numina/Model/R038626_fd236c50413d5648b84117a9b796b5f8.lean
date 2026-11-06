import Mathlib

theorem algebra_198405 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : (1 - 1 / 4 : ℚ) * x = (1 - 2 / 5 : ℚ) * y + 2) :
    y = 18 := by
  have eq1 : (3 / 4 : ℚ) * x = (3 / 5 : ℚ) * y + 2 := by
    linarith
  have eq2 : (15 : ℚ) * x = (12 : ℚ) * y + (40 : ℚ) := by
    linarith [eq1]
  have eq3 : 15 * (x : ℚ) = 12 * (y : ℚ) + 40 := by
    linarith [eq2]
  have eq4 : (15 * (x : ℤ) : ℚ) = (12 * (y : ℤ) + 40 : ℚ) := by
    exact_mod_cast eq3
  have eq5 : 15 * (x : ℤ) = 12 * (y : ℤ) + 40 := by
    exact_mod_cast eq4
  omega