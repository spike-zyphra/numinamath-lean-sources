import Mathlib

theorem number_theory_8964 :
  IsGreatest {m : ℕ | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, m = k ^ 2 ∧ m = 4 * (n ^ 4 + n ^ 3 + n ^ 2 + n + 1)} 484 := by
  constructor
  · -- Show 484 is in the set
    use 3
    constructor
    · norm_num -- 0 < 3
    use 22
    all_goals norm_num -- Show 484 = 22 ^ 2 ∧ 484 = 4 * (3 ^ 4 + 3 ^ 3 + 3 ^ 2 + 3 + 1)
  · -- Show 484 is the greatest
    intro m hm
    rcases hm with ⟨n, hn_pos, k, hk1, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ^ 2 > 484 := by
      nlinarith
    have h2 : k > 22 := by
      nlinarith
    have h3 : n > 3 := by
      by_contra h
      push_neg at h
      interval_cases n <;> try { 
        norm_num at hk2 
        all_goals { 
          have : k ≤ 22 := by nlinarith 
          interval_cases k <;> omega 
        }
      }
    -- For n ≥ 4, we will show that k is between (2n² + n) and (2n² + n + 1), contradiction as it's integer.
    have h4 : k < 2 * n ^ 2 + n + 1 := by
      nlinarith [sq_nonneg (k - (2 * n ^ 2 + n) : ℤ), sq_nonneg ((k + (2 * n ^ 2 + n)) : ℤ), sq_nonneg ((n : ℤ) - 3)]
    -- K lower bound
    have h5 : k > 2 * n ^ 2 + n := by
      nlinarith [sq_nonneg (k - (2 * n ^ 2 + n) : ℤ), sq_nonneg ((k + (2 * n ^ 2 + n)) : ℤ), sq_nonneg ((n : ℤ) - 3)]
    linarith