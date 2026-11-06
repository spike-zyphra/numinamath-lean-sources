import Mathlib

theorem number_theory_274813 (x y : ℕ) (h₀ : x > 0) (h₁ : y > 0)
    (h₂ : Nat.digits 10 x = Nat.digits 10 y) (h₃ : x / (Nat.digits 10 x).sum = y / (Nat.digits 10 y).sum + 1)
    (h₄ : x * y = (Nat.digits 10 x).sum * (Nat.digits 10 y).sum) :
    x = 18 := by 
  have h5 : x = y := by
    have h6 : Nat.digits 10 x = Nat.digits 10 y := h₂
    have h7 : x = y := by
      rw [← Nat.ofDigits_digits 10 x, ← Nat.ofDigits_digits 10 y]
      simp [h6]
    exact h7
  rw [h5] at h₃
  omega