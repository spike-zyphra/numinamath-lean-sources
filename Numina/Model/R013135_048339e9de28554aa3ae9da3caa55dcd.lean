import Mathlib

open Real

theorem algebra_199646 (a : ℕ → ℝ) (ha1 : a 1 = 1.5)
    (han : ∀ n > 1, a n = 1 / (n ^ 2 - 1)) :
    IsLeast {n | 1 ≤ n ∧ |∑ i in Finset.Icc 1 n, a i - 2.25| < 0.01} 100 := by
  constructor
  · -- Show 100 is in the set
    constructor
    · norm_num -- Show 1 ≤ 100
    · -- Show |∑ i in Finset.Icc 1 100, a i - 2.25| < 0.01
      norm_num [Finset.sum_Icc_succ_top, ha1, han]
      all_goals norm_num [abs_lt]
      all_goals norm_num
  · -- Show that any n in the set is at least 100
    intro n hn
    rcases hn with ⟨hn1, hne⟩
    by_contra h
    push_neg at h
    have h2 : n ≤ 99 := by omega

    have h3 : n ≤ 99 := h2

    have h4 : n < 100 := by omega

    have h5 : |∑ i in Finset.Icc 1 n, a i - 2.25| ≥ 0.01 := by
      by_cases h5 : n < 2
      · -- n = 1
        have : n = 1 := by omega
        rw [this]
        norm_num [abs, ha1]
        all_goals norm_num [abs]
        all_goals norm_num
      · -- 2 ≤ n ≤ 99
        have hn2 : n ≥ 2 := by omega
        have : n ≤ 99 := h3
        have h6 : n ≤ 99 := h3
        have h7 : n < 100 := by omega
        -- Use the formula for the sum
        have h8 : ∀ n : ℕ, n ≥ 1 → ∑ i in Finset.Icc 1 n, a i = 2.25 - (1 / (2 * (n : ℝ)) + 1 / (2 * ((n + 1 : ℕ) : ℝ))) := by
          intro n hn1
          induction n with
          | zero => linarith
          | succ n ih =>
            cases n with
            | zero => 
              norm_num [ha1]
              all_goals norm_num
            | succ n =>
              rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
              all_goals simp [ha1, han]
              all_goals field_simp
              <;> ring_nf <;> field_simp
              <;> norm_num
              all_goals ring_nf
              all_goals norm_num

        specialize h8 n (by omega)
        rw [h8] at hne
        rw [abs_lt] at hne
        -- Show contradiction for all n from 2 to 99
        by_cases h5 : n ≤ 99
        · -- Now n from 2 to 99
          interval_cases n <;> norm_num at hne ⊢
          <;> norm_num [abs_lt] at hne ⊢ <;> try norm_num at hne ⊢
          <;> try { linarith }
          all_goals norm_num
          all_goals norm_num
          all_goals try { linarith }
          all_goals norm_num
        all_goals norm_num at hne ⊢
        all_goals try { linarith }
    linarith