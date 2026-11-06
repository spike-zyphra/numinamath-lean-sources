import Mathlib

theorem number_theory_256896 (a d : ℕ) (h₀ : a < 10) (h₁ : a + d * 99 = 100)
    (h₂ : a + d * 3099 = 3103) :
    d = 1 := by 
  omega