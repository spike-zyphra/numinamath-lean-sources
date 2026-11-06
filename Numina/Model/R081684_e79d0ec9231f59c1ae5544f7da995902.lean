import Mathlib

theorem algebra_51824 {f s j r : ℕ}
    (h₀ : f * 4 = s * 5) (h₁ : s * 8 = j * 7) (h₂ : j * 7 = r * 9)
    (h₃ : f + s + j + r = 2158) :
    f = 630 := by 
  omega