import Mathlib

theorem algebra_241119 (total : ℕ) (h1 : (7 / 20 : ℚ) * total + (3 / 5 : ℚ) * (total - (7 / 20 : ℚ) * total) + 260 = total) :
    total = 1000 := by
  have h2 : (total : ℚ) = 1000 := by 
    linarith
  exact_mod_cast h2