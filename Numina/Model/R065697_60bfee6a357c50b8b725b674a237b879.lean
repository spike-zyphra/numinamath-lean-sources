import Mathlib

theorem number_theory_173434 (g s b : ℕ)
    (h₀ : g + s + b = 42)
    (h₁ : s = 63 / 3)
    (h₂ : b > 60 / 6 ∧ b < 60 / 5)
    (h₃ : g > 0) :
    g = 10 := by 
  norm_num at h₁ 
  norm_num at h₂ 
  omega