import Mathlib

theorem number_theory_993 (c d a b : ℕ) (h₀ : c < 10) (h₁ : d < 10)
    (h₂ : a < 10) (h₃ : b < 10) (h₄ : Nat.factorial 34 = 29523279900000000 + 1000000000 * c + 100000000 * d + 10000000 * a + 1000000 * b) :
    c = 3 ∧ d = 2 ∧ a = 0 ∧ b = 0 := by
  norm_num [Nat.factorial] at h₄
  omega