import Mathlib

theorem algebra_254014 (a b c d : ℤ) (h₀ : (a + b + c) / 3 + d = 17) (h₁ : (a + b + d) / 3 + c = 21)
    (h₂ : (a + c + d) / 3 + b = 23) (h₃ : (b + c + d) / 3 + a = 29) :
    max (max a b) (max c d) = 21 := by 
  have h4 : a = 21 := by
    omega 
  have h5 : b = 12 := by
    omega
  have h6 : c = 9 := by
    omega
  have h7 : d = 3 := by
    omega
  simp [h4, h5, h6, h7]