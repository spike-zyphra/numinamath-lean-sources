import Mathlib

theorem algebra_12989 :
    IsGreatest {x | ∀ n, (Nat.digits 10 n).length = 2 → (Nat.digits 10 n).headI = (Nat.digits 10 n).tail.headI → x ∣ n} 11 := by
  constructor
  · -- Show 11 is in the set
    show ∀ n, (Nat.digits 10 n).length = 2 → (Nat.digits 10 n).headI = (Nat.digits 10 n).tail.headI → 11 ∣ n
    intro n hn1 hn2
    by_cases h : n < 100
    · -- n < 100
      interval_cases n <;> norm_num at hn1 hn2 ⊢ <;> omega
    · -- n ≥ 100
      exfalso
      have h1 : (Nat.digits 10 n).length > 2 := by
        have h2 : n ≥ 100 := by
          omega
        have h3 : (Nat.digits 10 n).length > 2 := by
          have h4 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
            rw [Nat.digits_len]
            all_goals omega
          rw [h4]
          have h5 : Nat.log 10 n ≥ 2 := by
            have h6 : n ≥ 100 := by
              omega
            have h7 : 10 ^ 2 ≤ n := by
              nlinarith
            have h8 : Nat.log 10 n ≥ 2 := by
              apply Nat.le_log_of_pow_le (by omega) (by omega)
            linarith
          omega
        linarith
      omega
  · -- Show 11 is greatest in the set
    intro x hx
    have h1 : x ∣ 11 := by 
      have h2 := hx 11 (by norm_num) (by norm_num)
      norm_num at h2 ⊢
      exact h2
    have h2 : x ≤ 11 := by
      exact Nat.le_of_dvd (by norm_num) h1
    linarith