import Mathlib

theorem algebra_19975 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (Nat.digits 10 n).sum = 13) (h₃ : n - (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 27) :
    n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 143 := by 
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₂ h₃ ⊢ <;> all_goals omega