import Mathlib

theorem algebra_189086 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (Nat.digits 10 n).sum = 13) (h₃ : ∃ k, k < 100 ∧ k > 9 ∧
    n - (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = k ∧ k % 10 = 7) :
    n = 85 := by
  rcases h₃ with ⟨k, hk1, hk2, h₄, h₅⟩
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₂ h₄ h₅ ⊢ <;> omega