import Mathlib

theorem algebra_277704 {x y : ℕ} (h : x = (2 / 3 : ℚ) * y) (h' : x + y = 150) :
    x = y - 30 := by 
  have eq1 : (x : ℚ) + (y : ℚ) = (150 : ℚ) := by 
    exact_mod_cast h'
  have eq2 : (x : ℚ) = (2 / 3 : ℚ) * (y : ℚ) := by 
    exact_mod_cast h
  have eq3 : (y : ℚ) = 90 := by 
    linarith [eq1, eq2]
  have eq4 : (x : ℚ) = 60 := by 
    rw [eq3] at eq2
    linarith
  have eq5 : y = 90 := by 
    exact_mod_cast eq3
  have eq6 : x = 60 := by 
    exact_mod_cast eq4
  have eq7 : (x : ℕ) = y - 30 := by 
    omega
  exact eq7