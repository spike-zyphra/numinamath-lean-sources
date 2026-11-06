import Mathlib

theorem number_theory_31361 (a b c d e f : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a + b = c + d) (h₄ : b + c = a + e) (h₅ : c + d = b + f) (h₆ : d + e = a + f)
    (h₇ : e + f = b + c) (h₈ : Nat.Prime d) (h₉ : Nat.Prime e) (h₁₀ : Nat.Prime f) :
    (d + e + f) / 3 = 14 := by
  have h11 : e = c := by 
    omega
  have h12 : a = b := by 
    omega
  have h13 : a = b := h12
  have h14 : a ≠ b := h₀
  contradiction