import Mathlib

theorem number_theory_129502 {n : ℕ} (hn : n > 0) (h : (1 / 11 : ℚ) * n = (1 / 14 : ℚ) * (n - 1) + 1) :
    n = 12 ∨ n = 13 := by
  have h1 : (n : ℚ) > 0 := by
    exact_mod_cast hn

  have eq1 : (1 / 11 : ℚ) * (n : ℚ) = (1 / 14 : ℚ) * ((n : ℚ) - 1) + 1 := by 
    nlinarith

  have eq2 : 14 * (n : ℚ) = 11 * ((n : ℚ) - 1) + 154 := by
    field_simp at eq1 ⊢
    linarith
  
  have eq3 : 3 * (n : ℚ) = 143 := by
    linarith
  
  have eq4 : (n : ℚ) = (143 / 3 : ℚ) := by 
    linarith
  
  have h4 : (n : ℚ) * 3 = 143 := by 
    linarith
  
  have h5 : (n : ℤ) * 3 = 143 := by 
    exact_mod_cast h4
  
  omega