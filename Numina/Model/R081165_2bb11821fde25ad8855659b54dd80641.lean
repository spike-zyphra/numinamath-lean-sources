import Mathlib

theorem algebra_63954 (a b : ℝ) (h : ∃ d, a + d = 6 ∧ 6 + d = b) : a + b = 12 := by 
  rcases h with ⟨d, h1, h2⟩
  linarith