import Mathlib

theorem algebra_253079 (n : ℕ) (h : ∃ a d, a > 0 ∧ d > 0 ∧
    (n.choose 0) = a ∧ (n.choose 1) = a + d ∧ (n.choose 2) = a + 2 * d) :
    {k | ∃ m : ℤ, (n.choose k) = m}.encard = 3 := by
  rcases h with ⟨a, d, ha, hd, h1, h2, h3⟩
  have h1' : n.choose 0 = 1 := by 
    simp [Nat.choose_zero_right]
  have eq1 : a = 1 := by 
    linarith [h1, h1']
  have h2' : n.choose 1 = n := by 
    cases n with 
    | zero => simp [Nat.choose_one_right]
    | succ n => 
      simp [Nat.choose_one_right]
  have eq2 : a + d = n := by 
    linarith [h2, h2']
  have eq3 : d = n - 1 := by 
    omega
  have h3' : n.choose 2 = (n * (n - 1) ) / 2 := by 
    cases n with 
    | zero => simp [Nat.choose_two_right]
    | succ n => 
      cases n with 
      | zero => simp [Nat.choose_two_right]
      | succ n => 
        simp [Nat.choose_two_right, Nat.mul_div_cancel_left] 
        <;> omega
  rw [h3'] at h3
  rw [eq1] at h3
  rw [eq3] at h3
  have h4 : (n * (n - 1)) / 2 = 2 * (n : ℕ) - 1 := by 
    omega
  have h5 : n ≥ 2 := by 
    omega 
  have h9 : (n * (n - 1)) / 2 ≠ 2 * n - 1 := by 
    by_cases h11 : n ≤ 6 
    · interval_cases n <;> omega 
    · 
      push_neg at h11 
      have h11 : n ≥ 7 := by linarith 
      have h66 : (n * (n - 1)) / 2 > 2 * n - 1 := by 
        have h66 : n * (n - 1) ≥ 2 * (2 * n - 1) + 2 := by 
          have h22 : n ≥ 7 := by linarith 
          have : n * (n - 1) = n^2 - n := by 
            cases n with 
            | zero => linarith 
            | succ n => 
              simp [Nat.pow_two, Nat.mul_sub_left_distrib, Nat.mul_comm] 
              <;> ring_nf <;> omega 
          nlinarith [sq_nonneg (n - 5 : ℤ), sq_nonneg (n : ℤ), sq_pos_of_pos (show (0: ℕ) < 2 by norm_num)]
        have h77 : (n * (n - 1)) / 2 ≥ (2 * (2 * n - 1) + 2) / 2 := by 
            apply Nat.div_le_div_right 
            all_goals linarith 
        have h88 : (2 * (2 * n - 1) + 2) / 2 = 2 * n - 1 + 1 := by 
          cases n with 
          | zero => linarith 
          | succ n => 
            cases n with 
            | zero => linarith 
            | succ n => 
              simp [Nat.add_assoc, Nat.mul_sub_left_distrib, Nat.mul_add] 
              <;> ring_nf <;> omega 
        omega 
      omega 
  contradiction