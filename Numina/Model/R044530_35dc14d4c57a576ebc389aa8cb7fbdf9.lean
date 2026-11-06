import Mathlib

theorem number_theory_130847 (n : ℕ) (h₀ : n > 0) (h₁ : (Nat.digits 3 n).length = 3)
    (h₂ : (Nat.digits 3 n).headI > (Nat.digits 3 n).tail.headI) (h₃ : (Nat.digits 3 n).tail.headI > (Nat.digits 3 n).tail.tail.headI)
    (h₄ : Odd (Nat.ofDigits 3 (List.reverse (Nat.digits 3 n)) + n)) :
    n = 843 ∨ n = 932 ∨ n = 942 := by

  have h6 : n < 27 := by
    by_contra h
    push_neg at h
    have h7 : (Nat.digits 3 n).length > 3 := by
      have h8 : n ≥ 27 := by omega
      have h9 : (Nat.digits 3 n).length = Nat.log 3 n + 1 := by
        rw [Nat.digits_len]
        all_goals omega
      rw [h9]
      have h10 : Nat.log 3 n ≥ 3 := by
        have h11 : 3 ^ 3 ≤ n := by omega
        exact Nat.le_log_of_pow_le (by norm_num) h11
      omega
    omega
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ h₃ h₄ ⊢ <;> tauto