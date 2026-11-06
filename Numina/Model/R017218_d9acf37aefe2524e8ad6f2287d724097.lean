import Mathlib

theorem number_theory_188480 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : n * 72 = m * 54) (h₃ : n + m = 61) :
    n * 72 = 216 := by
  have eq1 : m = 61 - n := by 
    omega
  rw [eq1] at h₂
  omega