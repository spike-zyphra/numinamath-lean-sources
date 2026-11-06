import Mathlib

theorem number_theory_14544 : IsGreatest {b : ℕ | 2 ≤ b ∧ (Nat.digits b (Nat.ofDigits b [1, 1] ^ 4)).sum ≠ 2 ^ 4} 6 := by 
  constructor
  · constructor
    · norm_num
    · native_decide
  · intro b hb
    rcases hb with ⟨hb1, hb2⟩
    by_contra h
    push_neg at h
    have h1 : Nat.digits b (Nat.ofDigits b [1, 1] ^ 4) = [1, 4, 6, 4, 1] := by
      have h2 : b ≥ 7 := by omega
      have h3 : Nat.ofDigits b [1, 1] = b + 1 := by
        simp [Nat.ofDigits, add_assoc]
        all_goals linarith
        all_goals linarith
      rw [h3]
      have h4 : (b + 1) ^ 4 = b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1 := by ring
      rw [h4]
      have h5 : Nat.digits b (b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1) = [1, 4, 6, 4, 1] := by
        have h6 : b ≥ 7 := h2
        have h7 : b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1 = b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1 := by rfl
        rw [h7]
        have h8 : Nat.ofDigits b [1, 4, 6, 4, 1] = b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1 := by
          simp [Nat.ofDigits, add_mul, mul_add, pow_succ, pow_zero]
          <;> ring_nf <;> omega
        have h9 : Nat.digits b (b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1) = [1, 4, 6, 4, 1] := by
          rw [←h8]
          rw [Nat.digits_ofDigits]
          all_goals
            simp_all
            all_goals omega
        exact h9
      exact h5
    have h6 : (Nat.digits b (Nat.ofDigits b [1, 1] ^ 4)).sum = 16 := by
      rw [h1]
      norm_num
    have h5 : (Nat.digits b (Nat.ofDigits b [1, 1] ^ 4)).sum ≠ 2 ^ 4 := hb2
    norm_num at h5
    all_goals
      try { tauto }
      try { linarith [h6, h5] }
      all_goals contradiction