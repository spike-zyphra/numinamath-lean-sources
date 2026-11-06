import Mathlib

theorem algebra_193285 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (Nat.digits 10 n).sum = 12) (h₃ : n + 36 = (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))) :
    n = 48 := by
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₂ h₃ <;> omega