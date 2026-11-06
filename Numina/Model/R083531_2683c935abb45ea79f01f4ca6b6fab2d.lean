import Mathlib

theorem number_theory_279477 (A B C D E : ℕ) (h₀ : A < 10) (h₁ : B < 10) (h₂ : C < 10)
    (h₃ : D < 10) (h₄ : E < 10) (h₅ : (100000 + 10000 * A + 1000 * B + 100 * C + 10 * D + E) * 3 =
    100000 * A + 10000 * B + 1000 * C + 100 * D + 10 * E + 1) :
    A + B + C + D + E = 26 := by 
  have h8 : A = 4 := by
    omega
  have h9 : B = 2 := by 
    omega
  have h10 : C = 8 := by
    omega
  have h11 : D = 5 := by 
    omega
  have h12 : E = 7 := by 
    omega
  omega