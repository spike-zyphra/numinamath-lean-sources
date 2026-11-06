import Mathlib


theorem number_theory_280927 :
    {p : ℕ | ∃ k, p.Prime ∧ p = k^k + 1 ∧ (Nat.digits 10 p).length ≤ 19} =
    {2, 5, 257} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- If p is in the left side, then p is in the right side.
    rintro ⟨k, hp, h1, h2⟩
    have h3 : k ≤ 15 := by
      by_contra h
      push_neg at h
      have h4 : (Nat.digits 10 (k ^ k + 1)).length > 19 := by
        have h5 : k ≥ 16 := by omega
        have h6 : (Nat.digits 10 (k ^ k + 1)).length = Nat.log 10 (k ^ k + 1) + 1 := by
          rw [Nat.digits_len]
          all_goals
            omega
        rw [h6]
        have h7 : Nat.log 10 (k ^ k + 1) ≥ 19 := by
          have h8 : k ^ k + 1 ≥ 16 ^ 16 + 1 := by
            have h9 : k ≥ 16 := by omega
            have h10 : k ^ k ≥ 16 ^ 16 := by
              have h11 : k ≥ 16 := by omega
              have h14 : k ^ k ≥ 16 ^ 16 := by
                have h15 : k ^ k ≥ 16 ^ k := by
                  apply Nat.pow_le_pow_of_le_left
                  all_goals omega
                have h16 : 16 ^ k ≥ 16 ^ 16 := by
                  apply Nat.pow_le_pow_of_le_right
                  all_goals omega
                have h17 : k ^ k ≥ 16 ^ 16 := by
                  nlinarith [show k ^ k ≥ 16 ^ k from by linarith [h15], show 16 ^ k ≥ 16 ^ 16 by linarith [h16]]
                linarith
              linarith
            omega
          have h12 : 10 ^ 19 ≤ k ^ k + 1 := by
            have h13 : k ^ k + 1 ≥ 16 ^ 16 + 1 := h8
            have h14 : 16 ^ 16 + 1 ≥ 10 ^ 19 := by
              norm_num
            linarith
          have h13 : Nat.log 10 (k ^ k + 1) ≥ 19 := by
            apply Nat.le_log_of_pow_le (by omega) h12
          linarith
        omega
      have h5 : (Nat.digits 10 p).length ≤ 19 := h2
      rw [show p = k ^ k + 1 by linarith [h1]] at h5
      omega
    interval_cases k <;> norm_num [h1] at hp h2 ⊢
    <;> try { tauto }
  · -- If p is in the right side, then p is in the left side.
    rintro (rfl | rfl | rfl)
    · -- p = 2
      use 1
      all_goals
        norm_num
    · -- p = 5
      use 2
      all_goals
        norm_num
    · -- p = 257
      use 4
      all_goals
        norm_num