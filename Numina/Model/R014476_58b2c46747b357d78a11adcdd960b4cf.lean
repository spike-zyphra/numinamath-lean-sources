import Mathlib

theorem algebra_235326 (n : ℕ) (hn : n > 0) (h : (500 + n) * (1 - 49 / 100 : ℝ) = 500 * (1 - 50 / 100 : ℝ) + n) :
    n = 10 := by
  have h1 : (n : ℝ) > (0 : ℝ) := by
    exact_mod_cast (show (n : ℕ) > 0 by linarith)
  have eq1 : (500 + (n : ℝ)) * (1 - (49 / 100 : ℝ)) = 500 * (1 - (50 / 100 : ℝ)) + (n : ℝ) := by
    simpa using h
  norm_num at eq1 
  have eq2 : (n : ℝ) = (500 / 49 : ℝ) := by 
    linarith 
  have eq3 : (n : ℝ) = (500 / 49 : ℝ) := eq2 
  have eq4 : (n : ℝ) > (0 : ℝ) := by 
    linarith [show (n : ℝ) > (0 : ℝ) from h1]
  have eq5 : (n : ℕ) = 10 := by 
    have eq18 : (n : ℝ) = (500 / 49 : ℝ) := eq2
    have eq19 : (n : ℝ) = (500 / 49 : ℝ) := eq2 
    have eq20 : (n : ℝ) = (500 / 49 : ℝ) := eq2 
    have eq22 : (n : ℝ) > (10 : ℝ) := by
      linarith 
    have eq23 : n > 10 := by
      by_contra h
      push_neg at h
      have h24 : n ≤ 10 := by
        omega
      have h25 : (n : ℝ) ≤ (10 : ℝ) := by
        exact_mod_cast h24
      linarith 
    have eq24 : (n : ℝ) < (11 : ℝ) := by
      linarith 
    have eq25 : n < 11 := by
      by_contra h
      push_neg at h
      have h26 : n ≥ 11 := by
        omega
      have h27 : (n : ℝ) ≥ (11 : ℝ) := by
        exact_mod_cast h26
      linarith 
    have eq26 : n = 10 := by
      omega 
    exact_mod_cast eq26 
  exact_mod_cast eq5