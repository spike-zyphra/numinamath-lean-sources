import Mathlib

theorem number_theory_79074 (t : ℤ) (n : ℕ) (hn : n > 0) (h : n^2 + (4 * t - 1) * n + 4 * t^2 = 0) :
    IsSquare n := by 
  have h1 : (n : ℤ) > 0 := by 
    exact_mod_cast hn
  have h2 : (n : ℤ) ^ 2 + (4 * t - 1) * (n : ℤ) + 4 * t^2 = 0 := by 
    exact_mod_cast h
  have h3 : ( (n : ℤ) + 2 * t ) ^ 2 = (n : ℤ) := by 
    nlinarith
  have h4 : IsSquare ( (n : ℤ) ) := by
    have h5 : ( (n : ℤ) + 2 * t ) ^ 2 = (n : ℤ) := h3 
    exact ⟨ (n + 2 * t ), by nlinarith [h5] ⟩
  exact_mod_cast h4