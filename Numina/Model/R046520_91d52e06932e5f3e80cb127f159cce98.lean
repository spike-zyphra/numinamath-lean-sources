import Mathlib

theorem algebra_265775 (x : ℕ) (hx : x ≠ 0) (h1 : (1 / 5 : ℚ) * x + 12 + (1 / 4 : ℚ) * (x - (1 / 5 : ℚ) * x - 12) + 15 + (1 / 3 : ℚ) * (x - (1 / 5 : ℚ) * x - 12 - (1 / 4 : ℚ) * (x - (1 / 5 : ℚ) * x - 12)) + 18 = x - 42) :
    x = 190 := by
  have eq1 : (x : ℚ) = 405 / 2 := by
    linarith
  have eq2 : (x : ℚ) * 2 = 405 := by
    linarith [eq1]
  have eq3 : (x * 2 : ℚ) = 405 := by
    linarith [eq1]
  have eq4 : (x * 2 : ℤ) = 405 := by
    exact_mod_cast eq3
  have eq5 : x * 2 = 405 := by
    exact_mod_cast eq4
  -- Note that x * 2 is even. But 405 is odd. This creates a contradiction.
  have eq6 : x * 2 % 2 = 0 := by
    omega
  -- But 405 % 2 = 1
  have eq7 : x * 2 % 2 = 1 := by
    omega
  omega