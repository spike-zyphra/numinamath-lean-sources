import Mathlib

theorem number_theory_256870 (a b c d e f : ℕ) (h₀ : a < 10) (h₁ : b < 10)
    (h₂ : c < 10) (h₃ : d < 10) (h₄ : e < 10) (h₅ : f < 10)
    (h₆ : 7 ∣ 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f) :
    7 ∣ 100000 * b + 10000 * c + 1000 * d + 100 * e + 10 * f + a := by 
  omega