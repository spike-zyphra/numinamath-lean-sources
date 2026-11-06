import Mathlib

theorem number_theory_252822 :
    Set.ncard {n : ℕ | (Nat.digits 10 (n^2)).length + (Nat.digits 10 (n^3)).length = 10} = 53 := by
  have h1 : {n : ℕ | (Nat.digits 10 (n^2)).length + (Nat.digits 10 (n^3)).length = 10} = Finset.filter (fun n : ℕ => (Nat.digits 10 (n^2)).length + (Nat.digits 10 (n^3)).length = 10) (Finset.Icc 0 100) := by
    ext n
    simp at *
    intro h
    have h2 : n ≤ 100 := by
      by_contra h
      push_neg at h
      have h3 : n ≥ 101 := by omega
      have h4 : (Nat.digits 10 (n^2)).length + (Nat.digits 10 (n^3)).length > 10 := by
        have h7 : n ^ 2 ≥ 10000 := by
          have h8 : n ≥ 100 := by omega
          have h9 : n ^ 2 ≥ 100 ^ 2 := by
            apply Nat.pow_le_pow_of_le_left h8 2
          have h10 : 100 ^ 2 = 10000 := by norm_num
          linarith
        have h8 : (Nat.digits 10 (n^2)).length ≥ 5 := by
          have h9 : n ^ 2 ≥ 10000 := h7
          have h6_pos : 0 < n ^ 2 := by
            have : 0 < n := by linarith
            nlinarith
          rw [Nat.digits_len]
          all_goals
            have h11 : Nat.log 10 (n^2) ≥ 4 := by
                have h10 : n ^ 2 ≥ 10000 := h9
                have h12 : 10 ^ 4 ≤ n^2 := by linarith
                exact Nat.le_log_of_pow_le (by norm_num) h12
            omega
        have h9 : (Nat.digits 10 (n^3)).length ≥ 7 := by
          have h10 : n ^ 3 ≥ 1000000 := by
            have h11 : n ≥ 100 := by omega
            have h12 : n ^ 3 ≥ 100 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left h11 3
            have h13 : 100 ^ 3 = 1000000 := by norm_num
            linarith
          have h11_pos : 0 < n ^ 3 := by
            have : 0 < n := by linarith
            nlinarith
          rw [Nat.digits_len]
          all_goals
            have h12 : Nat.log 10 (n^3) ≥ 6 := by
                have h10 : n ^ 3 ≥ 1000000 := h10
                have h13 : 10 ^ 6 ≤ n^3 := by linarith
                exact Nat.le_log_of_pow_le (by norm_num) h13
            omega
        omega
      omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide