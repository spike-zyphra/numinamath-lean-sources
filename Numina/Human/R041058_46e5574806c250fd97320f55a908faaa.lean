import Mathlib

theorem number_theory_177148 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (n / 9 : ℝ) * 75 / 100 + 6 = n / 10) :
    n = 360 := by 
  have h2 : (n : ℝ) ≠ 0 := by exact_mod_cast h₀
  suffices (n : ℝ) = (360 : ℝ) by 
    norm_cast at this 
  linarith