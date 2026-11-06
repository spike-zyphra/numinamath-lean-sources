import Mathlib

theorem algebra_82249 (a b c d : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : d > 0) (h₄ : a * b + a * d + b * c + d * c = 40) :
    a + b + c + d = 13 ∨ a + b + c + d = 14 ∨ a + b + c + d = 22 ∨ a + b + c + d = 41 := by
  have eq1 : (a + c) * (b + d) = 40 := by 
    linarith [h₄]
  have h5 : a + c ≥ 2 := by
    omega
  have h6 : a + c ≤ 20 := by
    nlinarith [show (b + d) ≥ 2 from by omega, eq1]
  have h7 : b + d ≥ 2 := by
    omega
  have h8 : b + d ≤ 20 := by
    nlinarith [show (a + c) ≥ 2 from by omega, eq1]
  interval_cases h : a + c <;> omega