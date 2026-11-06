import Mathlib

theorem number_theory_60425 {N : ℕ} (hN : N > 0) (hN1 : (Nat.digits 9 N).length = 20)
    (hN2 : (Nat.digits 27 N).length = 13) :
    (Nat.digits 3 N).length = 39 := by

  have h1 : N ≥ 9 ^ 19 := by
    by_contra h
    push_neg at h
    have h2 : (Nat.digits 9 N).length < 20 := by
      have h3 : N < 9 ^ 19 := by
        linarith
      have h4 : (Nat.digits 9 N).length ≤ 19 := by
        have h5 : (Nat.digits 9 N).length = Nat.log 9 N + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        rw [h5]
        have h6 : Nat.log 9 N < 19 := by
          have h7 : 9 ^ 19 > N := by
            linarith
          have h8 : Nat.log 9 N < 19 := by
            apply Nat.log_lt_of_lt_pow
            all_goals linarith
          linarith
        omega
      omega
    linarith [hN1, h2]
  
  have h2 : N < 9 ^ 20 := by
    by_contra h
    push_neg at h
    have h3 : (Nat.digits 9 N).length > 20 := by
      have h4 : N ≥ 9 ^ 20 := by
        linarith
      have h5 : (Nat.digits 9 N).length ≥ 21 := by
        have h6 : (Nat.digits 9 N).length = Nat.log 9 N + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        rw [h6]
        have h7 : Nat.log 9 N ≥ 20 := by
          have h8 : N ≥ 9 ^ 20 := by
            linarith
          have h9 : Nat.log 9 N ≥ 20 := by
            apply Nat.le_log_of_pow_le (by norm_num) h8
          linarith
        omega
      omega
    linarith [hN1, h3]
  
  have h3 : N ≥ 27 ^ 12 := by
    by_contra h
    push_neg at h
    have h4 : (Nat.digits 27 N).length < 13 := by
      have h5 : N < 27 ^ 12 := by
        linarith
      have h6 : (Nat.digits 27 N).length ≤ 12 := by
        have h7 : (Nat.digits 27 N).length = Nat.log 27 N + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        rw [h7]
        have h8 : Nat.log 27 N < 12 := by
          have h9 : 27 ^ 12 > N := by
            linarith
          have h10 : Nat.log 27 N < 12 := by
            apply Nat.log_lt_of_lt_pow
            all_goals linarith
          linarith
        omega
      omega
    linarith [hN2, h4]
  
  have h4 : N < 27 ^ 13 := by
    by_contra h
    push_neg at h
    have h5 : (Nat.digits 27 N).length > 13 := by
      have h6 : N ≥ 27 ^ 13 := by
        linarith
      have h7 : (Nat.digits 27 N).length ≥ 14 := by
        have h8 : (Nat.digits 27 N).length = Nat.log 27 N + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        rw [h8]
        have h9 : Nat.log 27 N ≥ 13 := by
          have h10 : N ≥ 27 ^ 13 := by
            linarith
          have h11 : Nat.log 27 N ≥ 13 := by
            apply Nat.le_log_of_pow_le (by norm_num) h10
          linarith
        omega
      omega
    linarith [hN2, h5]

  have h5 : (Nat.digits 3 N).length = Nat.log 3 N + 1 := by
    rw [Nat.digits_len]
    all_goals
      omega

  rw [h5]

  have h6 : 3 ^ 38 ≤ N := by
    omega

  have h7 : N < 3 ^ 39 := by
    have h8 : N < 27 ^ 13 := by
      linarith
    have h9 : 27 ^ 13 = 3 ^ 39 := by
      norm_num
    have h10 : N < 3 ^ 39 := by
      nlinarith [h8, h9]
    linarith

  have h8 : Nat.log 3 N = 38 := by
    have h9 : 3 ^ 38 ≤ N := by
      linarith [h6]
    have h10 : N < 3 ^ 39 := by
      linarith [h7]
    have h11 : Nat.log 3 N = 38 := by
      have h12 : Nat.log 3 N = 38 := by
        rw [Nat.log_eq_iff]
        all_goals
          omega
      linarith [h12]
    linarith [h11]

  linarith [h8]