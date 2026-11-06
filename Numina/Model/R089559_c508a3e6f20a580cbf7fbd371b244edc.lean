import Mathlib

theorem algebra_218916 (n c g : ℕ)
    (h₀ : n + c + g = 1000)
    (h₁ : n > c)
    (h₂ : c > g)
    (h₃ : n * 3 = g * 5) :
    c ≤ 384 := by 
  omega