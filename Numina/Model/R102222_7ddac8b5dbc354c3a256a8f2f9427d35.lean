import Mathlib

theorem number_theory_116422 (n : ℕ) (hn : n > 0) :
    ∃ k, k^2 = n * 2^(n + 1) + 1 ↔ n = 3 := by
  by_cases h : n = 3
  · -- Assume n = 3, then 7 is the witness
    use 7
    simp [h]
    all_goals norm_num  -- handles the arithmetic goals
  · -- Assume n ≠ 3
    push_neg at h
    use 0  -- Use 0 as a witness
    constructor
    · -- Assume 0^2 = n * 2^(n + 1) + 1, prove n = 3
      intro h_eq
      have h1 : n * 2 ^ (n + 1) + 1 = 0 := by
        nlinarith
      have h2 : n * 2 ^ (n + 1) + 1 > 0 := by
        have hn1 : n > 0 := hn
        have h3 : n ≥ 1 := by linarith
        have h4 : 2 ^ (n + 1) ≥ 4 := by
          have hn1 : n ≥ 1 := by linarith
          have h5 : n + 1 ≥ 2 := by linarith
          have h6 : 2 ^ (n + 1) ≥ 2 ^ 2 := by
            apply Nat.pow_le_pow_of_le_right (by norm_num) h5
          norm_num at h6 ⊢
          linarith
        have h8 : n * 2 ^ (n + 1) ≥ 1 * 4 := by
          nlinarith [h3, h4, mul_pos (show 0 < n by linarith) (show 0 < 2 ^ (n + 1) by positivity)]
        linarith
      linarith
    · -- Assume n = 3, prove 0^2 = n * 2^(n + 1) + 1
      intro h_eq
      exfalso
      exact h h_eq