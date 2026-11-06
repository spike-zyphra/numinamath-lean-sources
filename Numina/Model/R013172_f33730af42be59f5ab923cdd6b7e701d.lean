import Mathlib

theorem number_theory_6347 (n : ℕ) :
    ¬ ∃ m, (n ^ 2 + 7 * n + 7) ^ 4 = m ^ 4 ∧
    (n ^ 2 + 7 * n + 7) ^ 4 < ∏ i ∈ Finset.range 8, (n + i) ∧
    ∏ i ∈ Finset.range 8, (n + i) < (n ^ 2 + 7 * n + 8) ^ 4 := by 
  rintro ⟨m, hm1, hm2, hm3⟩
  norm_num [Finset.prod_range_succ] at hm2 hm3
  have h1 : n ^ 2 + 7 * n + 7 < n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) := by
    nlinarith [sq_nonneg (n), sq_nonneg (n + 1), sq_nonneg (n + 2), sq_nonneg (n + 3), 
          sq_nonneg (n + 4), sq_nonneg (n + 5), sq_nonneg (n + 6), sq_nonneg (n + 7), 
          mul_nonneg (show 0 ≤ n by omega) (show 0 ≤ n + 1 by omega),
          mul_nonneg (show 0 ≤ n + 1 by omega) (show 0 ≤ n + 2 by omega),
          mul_nonneg (show 0 ≤ n + 2 by omega) (show 0 ≤ n + 3 by omega),
          mul_nonneg (show 0 ≤ n + 3 by omega) (show 0 ≤ n + 4 by omega),
          mul_nonneg (show 0 ≤ n + 4 by omega) (show 0 ≤ n + 5 by omega),
          mul_nonneg (show 0 ≤ n + 5 by omega) (show 0 ≤ n + 6 by omega),
          mul_nonneg (show 0 ≤ n + 6 by omega) (show 0 ≤ n + 7 by omega)]
  have h2 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) < (n ^ 2 + 7 * n + 8) ^ 4 := by 
    nlinarith [sq_nonneg (n), sq_nonneg (n + 1), sq_nonneg (n + 2), sq_nonneg (n + 3), 
          sq_nonneg (n + 4), sq_nonneg (n + 5), sq_nonneg (n + 6), sq_nonneg (n + 7), 
          mul_nonneg (show 0 ≤ n by omega) (show 0 ≤ n + 1 by omega),
          mul_nonneg (show 0 ≤ n + 1 by omega) (show 0 ≤ n + 2 by omega),
          mul_nonneg (show 0 ≤ n + 2 by omega) (show 0 ≤ n + 3 by omega),
          mul_nonneg (show 0 ≤ n + 3 by omega) (show 0 ≤ n + 4 by omega),
          mul_nonneg (show 0 ≤ n + 4 by omega) (show 0 ≤ n + 5 by omega),
          mul_nonneg (show 0 ≤ n + 5 by omega) (show 0 ≤ n + 6 by omega),
          mul_nonneg (show 0 ≤ n + 6 by omega) (show 0 ≤ n + 7 by omega)]
  -- production of linarith facts using both concatenants
  have h3 : n ^ 2 + 7 * n + 7 < m := by 
    by_contra h 
    push_neg at h 
    have h4 : m ≤ n ^ 2 + 7 * n + 7 := by 
      omega 
    have h5 : m ^ 4 ≤ (n ^ 2 + 7 * n + 7) ^ 4 := by 
      apply Nat.pow_le_pow_left 
      all_goals nlinarith 
    nlinarith 
  have h4 : m < n ^ 2 + 7 * n + 8 := by 
    by_contra h 
    push_neg at h 
    have h7 : m ≥ n ^ 2 + 7 * n + 8 := by 
      omega 
    have h8 : m ^ 4 ≥ (n ^ 2 + 7 * n + 8) ^ 4 := by 
      apply Nat.pow_le_pow_left 
      all_goals nlinarith 
    nlinarith 
  nlinarith [sq_nonneg (m - (n ^ 2 + 7 * n + 7)), sq_nonneg (m + (n ^ 2 + 7 * n + 7)), 
          sq_nonneg ((n ^ 2 + 7 * n + 7) ^ 2 - m ^ 2)]