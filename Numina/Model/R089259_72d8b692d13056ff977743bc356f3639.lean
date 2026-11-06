import Mathlib

theorem number_theory_199741 {n : ℕ} (h₀ : n > 400) (h₁ : n < 500)
    (h₂ : (Nat.digits 10 n).sum = 9) (h₃ : n = (47 / 36 : ℚ) * (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))) :
    n = 423 := by
  have h4 : n ≤ 499 := by linarith
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₂ h₃ ⊢ <;> all_goals
    { 
      try { trivial }
      <;> norm_num at h₂ h₃ <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at *
      <;> omega
    }