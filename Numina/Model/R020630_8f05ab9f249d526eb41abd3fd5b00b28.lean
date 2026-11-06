import Mathlib

theorem number_theory_19021 :
    IsLeast {n | n > 10 ∧ ∃ k, n = k^2 ∧ ∃ m, n = m^3} 64 := by
  constructor
  · -- Show that 64 is in the set
    constructor
    · norm_num
    · refine ⟨8, by norm_num, ?_⟩
      refine ⟨4, by norm_num⟩
  · -- Show that 64 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn1, k, hk1, m, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 8 := by
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (m : ℕ), pow_two_nonneg (k : ℕ), pow_two_nonneg (m : ℕ)]
    have h2 : m ≤ 3 := by
      -- Note that n = m^3 and n < 64 (from h).
      -- So m^3 < 64, which implies m ≤ 3 for m : ℕ.
      -- We can prove this by contradiction. Assume m ≥ 4.
      -- Then m^3 ≥ 4^3 = 64. But n = m^3, so n ≥ 64.
      -- This contradicts n < 64. So m ≤ 3 must hold.
      -- nlinarith can establish this.
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (m : ℕ), hk1, hk2, h, mul_nonneg (show (0 : ℕ) ≤ k by omega) (show (0 : ℕ) ≤ k by omega)]
    interval_cases k <;> interval_cases m <;> omega