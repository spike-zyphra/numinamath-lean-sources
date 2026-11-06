import Mathlib

theorem number_theory_130847 (n : ℕ) (h₀ : n > 0) (h₁ : (Nat.digits 3 n).length = 3)
    (h₂ : (Nat.digits 3 n).headI > (Nat.digits 3 n).tail.headI) (h₃ : (Nat.digits 3 n).tail.headI > (Nat.digits 3 n).tail.tail.headI)
    (h₄ : Odd (Nat.ofDigits 3 (List.reverse (Nat.digits 3 n)) + n)) :
    n = 843 ∨ n = 932 ∨ n = 942 := by
        have h5 : n < 27 := by
            have h_length : (Nat.digits 3 n).length = 3 := h₁
            by_contra h
            push_neg at h
            have : n ≥ 27 := by linarith
            have h_digits : (Nat.digits 3 n).length ≥ 4 := by
                have h1 : n ≥ 27 := by linarith
                have h2 : Nat.log 3 n ≥ 3 := by
                    have h3 : 3 ^ 3 ≤ n := by linarith
                    exact Nat.le_log_of_pow_le (by norm_num) h3
                have h4 : (Nat.digits 3 n).length = Nat.log 3 n + 1 := by
                    rw [Nat.digits_len]
                    all_goals linarith
                linarith
            linarith
        interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₀ h₁ h₂ h₃ h₄ <;> omega