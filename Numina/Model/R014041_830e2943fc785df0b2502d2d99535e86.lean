import Mathlib

theorem algebra_196188 {x y : ℕ} (h : x + y = 70) (h1 : (5 / 9 : ℚ) * x + (7 / 17 : ℚ) * y = x - (5 / 9 : ℚ) * y) :
    x = 36 ∧ y = 34 := by
  have h2 : (x : ℚ) + (y : ℚ) = 70 := by
    exact_mod_cast h
  have eq1 : (37 : ℚ) * (y : ℚ) = (17 : ℚ) * (x : ℚ) := by
    linarith [h1, h2]
  have eq2 : 37 * (y : ℕ) = 17 * (x : ℕ) := by
    exact_mod_cast eq1
  have h5 : x * 17 = 37 * y := by
    linarith [eq2]
  have h6 : x ≤ 70 := by
    omega
  have h7 : y ≤ 70 := by
    omega
  interval_cases x <;> omega