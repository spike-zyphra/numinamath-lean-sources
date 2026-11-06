import Mathlib

theorem number_theory_7102 (n : ℕ) (h : n > 0) (h1 : (Nat.digits 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5))).length = 6)
    (h2 : List.Palindrome (Nat.digits 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)))) :
    n + (n + 1) + (n + 2) + (n + 3) + (n + 4) + (n + 5) = 224 := by
  have h3 : n ≤ 20 := by
    by_contra h4
    push_neg at h4
    have h4 : n ≥ 21 := by linarith
    have h4' : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 21 * 22 * 23 * 24 * 25 * 26 := by
      have h10 : n ≥ 21 := h4
      have h11 : n + 1 ≥ 22 := by linarith
      have h12 : n + 2 ≥ 23 := by linarith
      have h13 : n + 3 ≥ 24 := by linarith
      have h14 : n + 4 ≥ 25 := by linarith
      have h15 : n + 5 ≥ 26 := by linarith
      have h16 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 21 * 22 * 23 * 24 * 25 * 26 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      linarith
    have h5 : (Nat.digits 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5))).length > 6 := by
      have h61 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 10000000 := by
        have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 21 * 22 * 23 * 24 * 25 * 26 := h4'
        have h40 : 21 * 22 * 23 * 24 * 25 * 26 ≥ 10000000 := by norm_num
        linarith [h3, h40]
      have h31 : (Nat.digits 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5))).length ≥ 7 := by
        have h13 : (Nat.digits 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5))).length = Nat.log 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)) + 1 := by 
          rw [Nat.digits_len]
          all_goals 
            omega
        have h14 : Nat.log 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)) ≥ 6 := by
          have h15 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 10000000 := h61
          have h16 : 10 ^ (6 : ℕ) ≤ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) := by
            norm_num at h15 ⊢
            omega
          have h17 : Nat.log 10 (n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)) ≥ 6 := by 
            have h18 : 10 ^ 6 ≤ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) := by 
              omega
            exact Nat.le_log_of_pow_le (by norm_num) h18
          linarith
        omega
      omega
    linarith
  have h4 : n ≤ 20 := h3
  interval_cases n <;> norm_num at h1 h2 ⊢
  <;> try { trivial }
  all_goals 
    norm_num [List.Palindrome] at h2 ⊢
    <;> try { omega }
    <;> try { native_decide }