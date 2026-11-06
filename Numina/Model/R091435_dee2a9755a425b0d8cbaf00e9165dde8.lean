import Mathlib

theorem algebra_105 {n : ℕ} (hdigit : (Nat.digits 10 n).length = 2)
    (heq : n = 2 * (Nat.digits 10 n).prod) :
    n = 36 := by
  have h1 : n ≥ 10 := by
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hdigit <;> all_goals contradiction

  have h2 : n ≤ 99 := by
    by_contra h
    push_neg at h
    have h3 : (Nat.digits 10 n).length > 2 := by
      have h4 : n ≥ 100 := by omega
      have h5 : (Nat.digits 10 n).length > 2 := by
        have h6 : (Nat.digits 10 n).length ≥ 3 := by 
          have h7 : n ≥ 100 := by linarith
          have h8 : (Nat.digits 10 n).length ≥ 3 := by
            have h9 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
              rw [Nat.digits_len]
              all_goals linarith
            have h10 : Nat.log 10 n ≥ 2 := by 
              have h11 : 10 ^ 2 ≤ n := by omega
              have h12 : Nat.log 10 n ≥ 2 := by
                exact Nat.le_log_of_pow_le (by norm_num) h11
              linarith
            omega
          linarith
        linarith
      linarith
    linarith [hdigit, h3]

  interval_cases n <;> norm_num at heq hdigit <;> all_goals trivial