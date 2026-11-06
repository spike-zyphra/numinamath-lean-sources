import Mathlib

theorem algebra_281605 {r b : ℕ} (hb : b ≠ 0) (h : (r + b) * (2 / 5 : ℚ) = b) (h' : (r + b) * (3 / 5 : ℚ) = b + 5) :
    r + b = 25 := by
  have eq1 : (r + b : ℚ) * (2 / 5 : ℚ) = (b : ℚ) := by
    exact_mod_cast h
  have eq2 : (r + b : ℚ) * (3 / 5 : ℚ) = (b + 5 : ℚ) := by
    exact_mod_cast h'
  have eq3 : (r + b : ℚ) * 2 = 5 * (b : ℚ) := by 
    linarith
  have eq4 : (r + b : ℚ) * 3 = 5 * (b : ℚ) + 25 := by
    linarith
  have eq5 : (r + b : ℚ) = 25 := by
    linarith [eq3, eq4]
  have eq6 : r + b = 25 := by
    exact_mod_cast eq5
  exact eq6