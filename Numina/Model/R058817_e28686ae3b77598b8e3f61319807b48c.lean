import Mathlib

theorem algebra_95545 {n : ℕ} (hn : n ≠ 0) (h : (3 / 4 : ℚ) * n = (2 / 3 : ℚ) * (n - 6)) :
    n = 27 := by 
  have h1 : (n : ℚ) > 0 := by
    have hn' : (n : ℚ) > 0 := by
      exact_mod_cast (show 0 < (n : ℕ) by
        omega)
    linarith
  -- Solving the equation
  have eqn : (n : ℚ) = -48 := by
    linarith
  have h2 : (n : ℚ) ≥ (0 : ℚ) := by
    exact_mod_cast (show 0 ≤ (n : ℕ) by
      omega)
  -- This is a contradiction
  linarith