import Mathlib

theorem number_theory_22762 {n : ℕ} {s : Set ℕ}
    (hs : s = {m | m % 3 = 2 ∧ m % 4 = 0 ∧ m % 11 = 5})
    (hn : n ∈ s) (hclosest : ∀m ∈ s, m ≠ n → |(n - 200 : ℤ)| < |(m - 200 : ℤ)|):
    n = 236 := by
  rw [hs] at hn 
  rcases hn with ⟨h1, h2, h3⟩
  have h236 : 236 ∈ s := by
    rw [hs]
    constructor
    · norm_num -- 236 % 3 = 2 
    constructor
    · norm_num -- 236 % 4 = 0 
    · norm_num -- 236 % 11 = 5 
  -- Assume that n is not 236, we reach a contradiction
  by_cases h : n = 236 
  · exact h 
  · -- Assume n ≠ 236, apply hclosest to m = 236
    have h5 : 236 ≠ n := by 
      intro h'
      rw [h'] at h 
      contradiction 
    have h4 := hclosest 236 h236 h5 
    -- Then |n - 200| < |236 - 200| = 36
    norm_num at h4 
    -- Therefore, n is in the interval (164, 236)
    have h7 : (n : ℤ) > 164 := by 
      norm_num at h4 
      by_contra h'
      push_neg at h'
      have h7 : (n : ℤ) ≤ 164 := by linarith 
      have h8 : (n - 200 : ℤ) ≤ -36 := by 
        omega 
      have h9 : |(n - 200 : ℤ)| ≥ 36 := by 
        rw [abs_of_nonpos (by omega)]
        linarith 
      linarith 
    -- and n < 236 
    have h8 : (n : ℤ) < 236 := by 
      norm_num at h4 
      by_contra h'
      push_neg at h'
      have h7 : (n : ℤ) ≥ 236 := by linarith 
      have h8 : (n - 200 : ℤ) ≥ 36 := by 
        omega 
      have h9 : |(n - 200 : ℤ)| ≥ 36 := by 
        rw [abs_of_nonneg (by omega)]
        linarith 
      linarith 
    -- Now n is a solution in the interval (164, 236)
    -- Let's check that there is no solution in this interval
    have h9 : n > 164 := by 
      omega 
    have h10 : n < 236 := by 
      omega 
    interval_cases n <;> omega 
    all_goals norm_num at h1 h2 h3 
    all_goals omega