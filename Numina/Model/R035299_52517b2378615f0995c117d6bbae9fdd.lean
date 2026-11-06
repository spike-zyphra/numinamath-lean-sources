import Mathlib

open Real

theorem inequalities_90709 :
    Set.ncard {n : ℕ | 0 < n ∧ 1 + sqrt (n ^ 2 - 9 * n + 20) > sqrt (n ^ 2 - 7 * n + 12)} = 4 := by
  have h2 : {n : ℕ | 0 < n ∧ 1 + sqrt (n ^ 2 - 9 * n + 20) > sqrt (n ^ 2 - 7 * n + 12)} = {1, 2, 3, 4} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

    constructor
    · -- Assume h: 0 < n ∧ 1 + sqrt (n ^ 2 - 9 * n + 20) > sqrt (n ^ 2 - 7 * n + 12), prove {1, 2, 3, 4}
      intro h
      rcases h with ⟨hn_pos, h1⟩
      have h2 : n ≤ 4 := by
        by_contra h'
        push_neg at h'
        have hn_pos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
        have h3 : n ≥ 5 := by omega
        have hn5 : (n : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h3
        -- Use polynomial expressions
        have eq1 : ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20 : ℝ) = ((n : ℝ) - 4) * ((n : ℝ) - 5) := by
          nlinarith
        have eq2 : ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12 : ℝ) = ((n : ℝ) - 3) * ((n : ℝ) - 4) := by
          nlinarith
        have h4 : ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20 : ℝ) ≥ 0 := by
          rw [eq1]
          nlinarith [sq_nonneg ((n : ℝ) - 4), sq_nonneg ((n : ℝ) - 5)]
        have h5 : ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12 : ℝ) ≥ 0 := by
          rw [eq2]
          nlinarith [sq_nonneg ((n : ℝ) - 3), sq_nonneg ((n : ℝ) - 4)]
        have h6 : 0 < (n : ℝ) := by exact_mod_cast hn_pos
        have h4' : sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20) ≥ 0 := by positivity
        have h5' : sqrt ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12) ≥ 0 := by positivity
        have h6 : (1 + sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20)) > sqrt ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12) := by exact_mod_cast h1
        have h16 : (1 + sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20)) ^ 2 > (sqrt ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12) : ℝ) ^ 2 := by
          nlinarith [h6, h4', h5']
        have eq3 : (1 + sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20) : ℝ) ^ 2 = 1 + (n ^ 2 - 9 * n + 20 : ℝ) + 2 * sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20 : ℝ) := by
          ring_nf
          rw [Real.sq_sqrt]
          all_goals nlinarith
          all_goals norm_num
        have eq4 : (sqrt ((n : ℝ) ^ 2 - 7 * (n : ℝ) + 12) : ℝ) ^ 2 = (n ^ 2 - 7 * n + 12 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals nlinarith
          all_goals norm_num
        have final : (1 + (n ^ 2 - 9 * n + 20 : ℝ) + 2 * sqrt ((n : ℝ) ^ 2 - 9 * (n : ℝ) + 20 : ℝ) : ℝ) > (n ^ 2 - 7 * n + 12 : ℝ) := by
          nlinarith [eq3, eq4, h16, h4', h5']
        nlinarith [sq_nonneg ((n : ℝ) - 5), sq_nonneg ((n : ℝ) - 4)]
      interval_cases n <;> norm_num at h1 ⊢ <;> norm_num [Real.sqrt_pos, Real.sqrt_le_sqrt, Real.sqrt_lt_sqrt]
      <;> ring_nf <;> norm_num
      <;> try { nlinarith [Real.sqrt_nonneg 12, Real.sqrt_nonneg 6, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (12 : ℝ) > 0 by norm_num)] }
      <;> try { norm_num [Real.sqrt_pos, Real.sq_sqrt] }
      <;> try { linarith }
      <;> try { norm_num [Real.sqrt_pos, Real.sq_sqrt] }
    · -- Show that if n ∈ {1,2,3,4}, then n ∈ {n | 0 < n ∧ ...}
      rintro (rfl | rfl | rfl | rfl)
      -- Verify case n = 1
      · constructor
        · norm_num
        · have h1 : (1 + sqrt (1 ^ 2 - 9 * 1 + 20) : ℝ) > (sqrt (1 ^ 2 - 7 * 1 + 12) : ℝ) := by
            have h2 : sqrt (1 ^ 2 - 9 * 1 + 20) = sqrt 12 := by norm_num
            have h3 : sqrt (1 ^ 2 - 7 * 1 + 12) = sqrt 6 := by norm_num
            rw [h2, h3]
            have h4 : sqrt 12 = Real.sqrt 12 := by rfl
            have h5 : sqrt 6 = Real.sqrt 6 := by rfl
            have h6 : 1 + sqrt 12 > sqrt 6 := by
              have h7 : sqrt 12 > 0 := by positivity
              have h8 : sqrt 6 > 0 := by positivity
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 12, Real.sqrt_nonneg 6, sq_nonneg (sqrt 12 - sqrt 6), Real.sqrt_le_sqrt (show (6 : ℝ) ≤ (12 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
            nlinarith
          exact_mod_cast h1
      -- Verify case n = 2
      · constructor
        · norm_num
        · have h1 : (1 + sqrt (2 ^ 2 - 9 * 2 + 20) : ℝ) > (sqrt (2 ^ 2 - 7 * 2 + 12) : ℝ) := by
            have h2 : sqrt (2 ^ 2 - 9 * 2 + 20) = sqrt 6 := by norm_num
            have h3 : sqrt (2 ^ 2 - 7 * 2 + 12) = sqrt 2 := by norm_num
            rw [h2, h3]
            have h6 : 1 + sqrt 6 > sqrt 2 := by
              have h7 : sqrt 6 > 0 := by positivity
              have h8 : sqrt 2 > 0 := by positivity
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, sq_nonneg (sqrt 6 - sqrt 2), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            nlinarith
          exact_mod_cast h1
      -- Verify case n = 3
      · constructor
        · norm_num
        · have h1 : (1 + sqrt (3 ^ 2 - 9 * 3 + 20) : ℝ) > (sqrt (3 ^ 2 - 7 * 3 + 12) : ℝ) := by
            have h2 : sqrt (3 ^ 2 - 9 * 3 + 20) = sqrt 2 := by norm_num
            have h3 : sqrt (3 ^ 2 - 7 * 3 + 12) = (0 : ℝ) := by norm_num [Real.sqrt_eq_zero]
            rw [h2, h3]
            have h6 : 1 + sqrt 2 > (0 : ℝ) := by
              have h7 : sqrt 2 > 0 := by positivity
              linarith
            nlinarith
          exact_mod_cast h1
      -- Verify case n = 4
      · constructor
        · norm_num
        · have h1 : (1 + sqrt (4 ^ 2 - 9 * 4 + 20) : ℝ) > (sqrt (4 ^ 2 - 7 * 4 + 12) : ℝ) := by
            have h2 : sqrt (4 ^ 2 - 9 * 4 + 20) = (0 : ℝ) := by norm_num [Real.sqrt_eq_zero]
            have h3 : sqrt (4 ^ 2 - 7 * 4 + 12) = (0 : ℝ) := by norm_num [Real.sqrt_eq_zero]
            rw [h2, h3]
            norm_num
          exact_mod_cast h1
  rw [h2]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> tauto
  all_goals norm_num
  all_goals nlinarith