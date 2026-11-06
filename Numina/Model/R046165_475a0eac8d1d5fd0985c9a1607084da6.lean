import Mathlib

theorem number_theory_13905 : IsGreatest {s > 0 | ∃ k, s = k^2 + 5 ∧ ∃ n, s = n * (n + 7)} 294 := by
  constructor
  · -- Show 294 is in the set
    constructor
    · norm_num
    · -- Show existence of k, s = k^2 + 5 and existence of n, s = n * (n + 7)
      use 17
      constructor
      · norm_num
      · -- Show existence of n
        use 14
        all_goals norm_num
  · -- Show it's the greatest
    intro s hs
    rcases hs with ⟨hs_pos, k, hk1, n, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ^ 2 + 5 = n * (n + 7) := by
      nlinarith
    -- Derive upper bounds
    have h2 : k < n + 4 := by
      nlinarith [sq_nonneg ((k : ℕ) - (n + 3) : ℤ)]
    -- Derive upper bounds
    have h3 : n ≤ k + 3 := by
      nlinarith [sq_nonneg ((k : ℕ) - (n : ℕ) : ℤ)]
    have h4 : k < n + 4 := by
      nlinarith [sq_nonneg ((k : ℕ) - (n + 3) : ℤ)]
    -- Derive upper bounds
    have h5 : n ≤ 31 := by
      nlinarith [sq_nonneg ((k : ℕ) - (n + 3) : ℤ), sq_nonneg ((n - 31 : ℤ)), sq_nonneg ((k - 34 : ℤ)), mul_nonneg (show 0 ≤ k by positivity) (show 0 ≤ n by positivity), h]
    have h6 : k ≤ 35 := by
      nlinarith [h5, h1, mul_nonneg (show 0 ≤ k by positivity) (show 0 ≤ n by positivity)]
    interval_cases n <;> try { 
      omega 
    } 
    <;> try { 
      interval_cases k <;> omega 
    }