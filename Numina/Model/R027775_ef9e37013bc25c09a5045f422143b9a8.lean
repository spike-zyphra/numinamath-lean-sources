import Mathlib

theorem number_theory_91636 (n : ℤ) (hn : n ≠ 0) :
    ¬ ∃ m, m^2 = n^4 - 7 * n^2 + 1 := by
  rintro ⟨m, hm⟩
  have h1 : m^2 = n^4 - 7 * n^2 + 1 := by
    nlinarith
  have h2 : n^2 > 0 := by
    have h3 : n ≠ 0 := hn
    have h4 : n^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact h3
    linarith
  by_cases h4 : n^2 > 15
  · -- If n^2 > 15, then n^2 ≥ 16
    have h5 : n^2 ≥ 16 := by omega
    have h6 : (n^2 - 4 : ℤ) ^ 2 < m^2 := by
      nlinarith [sq_nonneg (n^2 - 16 : ℤ), h1, h5]
    have h7 : m^2 < (n^2 - 3 : ℤ) ^ 2 := by
      nlinarith [sq_nonneg (n^2 - 16 : ℤ), h1, h5]
    by_cases hm_pos : m ≥ 0
    · -- m ≥ 0
      have h9 : (n^2 - 4 : ℤ) < m := by
        nlinarith [show (n^2 - 4 : ℤ) ≥ 0 by nlinarith [h5], h6, sq_nonneg (m - (n^2 - 4 : ℤ) : ℤ)]
      have h10 : m < (n^2 - 3 : ℤ) := by
        nlinarith [show (n^2 - 3 : ℤ) ≥ 0 by nlinarith [h5], h7, sq_nonneg (m - (n^2 - 3 : ℤ) : ℤ)]
      omega
    · -- m < 0
      have hm_neg : m < 0 := by linarith
      have h9 : m < - (n^2 - 4 : ℤ) := by
        nlinarith [show (n^2 - 4 : ℤ) ≥ 0 by nlinarith [h5], h6, sq_nonneg (m + (n^2 - 4 : ℤ) : ℤ)]
      have h10 : - (n^2 - 3 : ℤ) < m := by
        nlinarith [show (n^2 - 3 : ℤ) ≥ 0 by nlinarith [h5], h7, sq_nonneg (m + (n^2 - 3 : ℤ) : ℤ)]
      omega
  · -- If n^2 ≤ 15
    have h4 : n^2 ≤ 15 := by
      omega
    have h5 : n ≤ 3 := by
      nlinarith [sq_nonneg (n : ℤ), h4]
    have h6 : n ≥ -3 := by
      nlinarith [sq_nonneg (n : ℤ), h4]
    interval_cases n <;> try { 
      norm_num at h1
      all_goals
      have h7 : m ≤ 4 := by
        nlinarith
      have h8 : m ≥ -4 := by
        nlinarith
      interval_cases m <;> omega
    }