import Mathlib

theorem number_theory_241674 (A B C D E F G H I : ℕ)
    (h₀ : A ≠ 0) (h₁ : B ≠ 0) (h₂ : C ≠ 0)
    (h₃ : D ≠ 0) (h₄ : E ≠ 0) (h₅ : F ≠ 0)
    (h₆ : G ≠ 0) (h₇ : H ≠ 0) (h₈ : I ≠ 0)
    (h₉ : A * 10 + B = 3) (h₁₀ : B * 10 + C = 5)
    (h₁₁ : D * 10 + E = 1) (h₁₂ : E * 10 + F = 9)
    (h₁₃ : G * 10 + H = 5) (h₁₄ : H * 10 + I = 3) :
    C = 9 := by 
  omega