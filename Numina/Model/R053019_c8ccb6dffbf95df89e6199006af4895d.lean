import Mathlib

theorem algebra_170198 (d t : ℝ) (ht : t = 7.5) (h : d / 4 = 7.5 ∧ d / 3 = 7.67) :
    d / (d / 4 + d / 3) = 7.8 := by 
  rcases h with ⟨h1, h2⟩
  linarith