import Mathlib

open Set

theorem number_theory_199312:
    { (m,n) : ℕ × ℕ | m^m + (m * n)^n =1984 } = { (4,3) } := by
  ext ⟨m, n⟩
  simp
  constructor
  · -- First, prove that (4,3) is the only solution.
    rintro H
    have h1 : m ≤ 12 := by
      by_contra h
      push_neg at h
      have h4 : m ≥ 13 := by omega
      have h3 : m ^ m ≥ 13 ^ 13 := by
        have h7 : m ≥ 13 := by omega
        have h8 : m ^ m ≥ m ^ 13 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h9 : m ^ 13 ≥ 13 ^ 13 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        linarith
      have h10 : m ^ m + (m * n) ^ n ≥ m ^ m := by linarith [show (m * n) ^ n ≥ 0 by positivity]
      linarith
    have h3 : n ≤ 12 := by
      by_contra h
      push_neg at h
      have h4 : n ≥ 13 := by omega
      by_cases hm : m > 0
      · have h4 : m ≥ 1 := by omega
        have h3 : (m * n) ^ n ≥ 13 ^ 13 := by
          have h5 : m * n ≥ 13 := by
            nlinarith [show n ≥ 13 by omega, show m ≥ 1 by omega]
          have h50 : (m * n) ^ n ≥ 13 ^ 13 := by
            have h13 : n ≥ 13 := by omega
            have h14 : m * n ≥ 13 := by
              nlinarith
            have h24 : (m * n) ^ n ≥ 13 ^ 13 := by
              have h15 : (m * n) ^ n ≥ (m * n) ^ 13 := by
                apply Nat.pow_le_pow_of_le_right
                all_goals nlinarith
              have h16 : (m * n) ^ 13 ≥ 13 ^ 13 := by
                apply Nat.pow_le_pow_of_le_left
                all_goals nlinarith
              linarith
            linarith
          linarith
        have h10 : m ^ m + (m * n) ^ n ≥ 13 ^ 13 := by linarith [show m ^ m ≥ 0 by positivity, h3]
        linarith
      · -- m ≤ 0, so m = 0
        have hm0 : m = 0 := by omega
        rw [hm0] at H
        have h3 : (0 : ℕ) ^ (0 : ℕ) + (0 * n) ^ n = 1984 := by
          simpa using H
        have h4 : (0 : ℕ) ^ (0 : ℕ) = 1 := by simp
        rw [h4] at h3
        by_cases hn' : n > 0
        · -- If n > 0, then (0 * n) ^ n = 0
          have h5 : (0 * n) ^ n = 0 := by
            have h5 : 0 * n = 0 := by ring
            rw [h5]
            have h7 : 0 ^ n = 0 := by
              apply Nat.zero_pow
              omega
            linarith
          rw [h5] at h3
          all_goals omega
        · -- n ≤ 0, so n = 0
          have hn0 : n = 0 := by omega
          rw [hn0] at h3
          norm_num at h3
    interval_cases m <;> interval_cases n
    <;> norm_num at H ⊢
    <;> try { tauto }
  · -- Second direction: if (m, n) = (4, 3), then it's a solution.
    rintro ⟨rfl, rfl⟩
    all_goals norm_num