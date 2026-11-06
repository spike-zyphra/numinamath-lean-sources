import Mathlib

theorem number_theory_137023 :
    Set.ncard {n : ℕ | (Nat.digits 10 n).length = 5 ∧ n % 10 = 6 ∧ 3 ∣ n} = 3000 := by 
  have h1 : {n : ℕ | (Nat.digits 10 n).length = 5 ∧ n % 10 = 6 ∧ 3 ∣ n} = Finset.filter (λ n => (Nat.digits 10 n).length = 5 ∧ n % 10 = 6 ∧ 3 ∣ n) (Finset.Icc 0 99999) := by 
    ext n 
    simp 
    intro h1 h2 h3 
    have h4 : n ≤ 99999 := by 
      by_contra h 
      push_neg at h 
      have h5 : (Nat.digits 10 n).length > 5 := by 
        have h6 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
          rw [Nat.digits_len]
          all_goals 
            omega 
        rw [h6]
        have h7 : Nat.log 10 n ≥ 5 := by 
          have h8 : 10 ^ 5 ≤ n := by 
            omega 
          exact Nat.le_log_of_pow_le (by linarith) h8 
        omega 
      omega 
    have h5 : n ≥ 10000 := by 
      by_contra h 
      push_neg at h 
      have h6 : (Nat.digits 10 n).length < 5 := by 
        have h7 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
          rw [Nat.digits_len]
          all_goals 
            omega 
        rw [h7]
        have h8 : Nat.log 10 n < 4 := by 
          have h9 : n < 10000 := by 
            omega 
          have h10 : Nat.log 10 n < 4 := by 
            apply Nat.log_lt_of_lt_pow
            all_goals 
              omega 
          omega 
        omega 
      omega 
    omega 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide