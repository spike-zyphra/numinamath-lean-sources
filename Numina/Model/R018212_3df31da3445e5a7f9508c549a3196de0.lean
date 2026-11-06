import Mathlib

theorem number_theory_288123 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : (Nat.digits 10 n).length = 3) (h₃ : (Nat.digits 10 m).length = 2)
    (h₄ : (Nat.digits 10 n).toFinset.card = 3) (h₅ : (Nat.digits 10 m).toFinset.card = 2)
    (h₆ : n - m = 976) : n + m = 996 := by

  have h7 : n = m + 976 := by 
    omega

  have h8 : m ≤ 99 := by 
    by_contra h 
    push_neg at h 
    have h9 : (Nat.digits 10 m).length > 2 := by
      have h10 : m > 99 := by 
        omega 
      have h11 : Nat.log 10 m ≥ 2 := by 
        have : m > 99 := by 
          omega 
        have h12 : 10 ^ 2 ≤ m := by 
          omega 
        have h13 : Nat.log 10 m ≥ 2 := by 
          apply Nat.le_log_of_pow_le (by linarith) (by linarith) 
        omega 
      have h14 : (Nat.digits 10 m).length = Nat.log 10 m + 1 := by 
        rw [Nat.digits_len]
        all_goals 
          omega 
      rw [h14]
      omega 
    omega

  have h9 : n ≤ 999 := by 
    by_contra h 
    push_neg at h 
    have h10 : (Nat.digits 10 n).length > 3 := by 
      have h11 : n > 999 := by 
        omega 
      have h12 : Nat.log 10 n ≥ 3 := by 
        have : n > 999 := by 
          omega 
        have h13 : 10 ^ 3 ≤ n := by 
          omega 
        have h14 : Nat.log 10 n ≥ 3 := by 
          apply Nat.le_log_of_pow_le (by linarith) (by linarith) 
        omega 
      have h13 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
        rw [Nat.digits_len]
        all_goals 
          omega 
      rw [h13]
      omega 
    omega

  have h10 : m ≤ 23 := by 
    omega

  have h11 : m ≥ 10 := by 
    by_contra h 
    push_neg at h 
    have h9 : m < 10 := by 
      omega 
    have h10 : (Nat.digits 10 m).length < 2 := by 
      interval_cases m <;> norm_num 
    omega

  interval_cases m <;> norm_num [h7] at h₄ h₆ h₅ h9 
  <;> omega