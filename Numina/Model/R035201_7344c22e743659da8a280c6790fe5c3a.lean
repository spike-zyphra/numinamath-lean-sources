import Mathlib

open Real

theorem algebra_234630 : ∑ i ∈ Finset.range 1009, sqrt (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3))) = (sqrt 2019 - 1) / sqrt 2 := by 
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, sqrt (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3))) = (sqrt (2 * n + 1) - 1) / sqrt 2 := by 
    intro n 
    have h2 : ∀ n : ℕ, ∑ i ∈ Finset.range n, sqrt (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3))) = (sqrt (2 * n + 1) - 1) / sqrt 2 := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ k ih => 
        rw [Finset.sum_range_succ, ih] 
        have h4 : sqrt (2 * (k : ℝ) + 2 - sqrt ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3))) = (sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2 := by 
          have h7 : (2 * (k : ℝ) + 2 - sqrt ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3))) = ((sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2) ^ 2 := by 
            have h9 : ((sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2) ^ 2 =
              ((sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) ^ 2) / 2 := by 
              field_simp 
              <;> ring 
            rw [h9] 
            have h10 : (sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) ^ 2 = 
              (sqrt (2 * (k + 1 : ℝ) + 1)) ^ 2 + (sqrt (2 * (k : ℝ) + 1)) ^ 2 - 2 * (sqrt (2 * (k + 1 : ℝ) + 1) * sqrt (2 * (k : ℝ) + 1)) := by 
              ring 
            rw [h10] 
            have h11 : (sqrt (2 * (k + 1 : ℝ) + 1)) ^ 2 = (2 * (k + 1 : ℝ) + 1) := by 
              apply Real.sq_sqrt 
              linarith 
            have h12 : (sqrt (2 * (k : ℝ) + 1)) ^ 2 = (2 * (k : ℝ) + 1) := by 
              apply Real.sq_sqrt 
              linarith 
            rw [h11, h12] 
            have h13 : sqrt (2 * (k + 1 : ℝ) + 1) * sqrt (2 * (k : ℝ) + 1) = sqrt ((2 * (k + 1 : ℝ) + 1) * (2 * (k : ℝ) + 1)) := by 
              rw [← Real.sqrt_mul (by positivity)] 
              all_goals positivity 
            rw [h13] 
            have h14 : (2 * (k + 1 : ℝ) + 1) * (2 * (k : ℝ) + 1) = (2 * (k : ℝ) + 1) * (2 * (k + 1 : ℝ) + 1) := by ring 
            rw [h14] 
            have h15 : (2 * (k : ℝ) + 1) * (2 * (k + 1 : ℝ) + 1) = (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by 
              ring_nf 
            rw [h15] 
            all_goals ring_nf <;> norm_num 
            all_goals try { linarith [Real.sqrt_nonneg ((2 * (k : ℝ) + 1) * (2 * (k + 1 : ℝ) + 1)), Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1)] }
            all_goals try { nlinarith [Real.sqrt_nonneg ((2 * (k : ℝ) + 1) * (2 * (k + 1 : ℝ) + 1)), Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1)] }
          rw [h7] 
          have h8 : 0 ≤ (sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2 := by 
            apply div_nonneg 
            · -- Show sqrt (2 * (↑k + 1) + 1) - sqrt (2 * ↑k + 1) ≥ 0 
              have h5 : sqrt (2 * (k + 1 : ℝ) + 1) ≥ sqrt (2 * (k : ℝ) + 1) := by 
                apply Real.sqrt_le_sqrt 
                nlinarith 
              linarith [Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1), Real.sqrt_nonneg (2 * (k : ℝ) + 1), h5] 
            · -- Show sqrt 2 ≥ 0 
              positivity 
          have h9 : sqrt (((sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2) ^ 2) = (sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2 := by 
            rw [Real.sqrt_sq (show 0 ≤ (sqrt (2 * (k + 1 : ℝ) + 1) - sqrt (2 * (k : ℝ) + 1)) / sqrt 2 by linarith [h8])] 
          rw [h9] 
        rw [h4] 
        field_simp 
        <;> ring_nf <;> norm_num [Real.sq_sqrt, Real.sqrt_mul_self] 
        <;> ring_nf <;> norm_num 
        all_goals try { ring } 
        all_goals try { nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1), Real.sq_sqrt (show (2 * (k : ℝ) + 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (2 * (k + 1 : ℝ) + 1) ≥ 0 by nlinarith), Real.sqrt_nonneg (2)] }
        all_goals try { linarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1), Real.sq_sqrt (show (2 * (k : ℝ) + 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (2 * (k + 1 : ℝ) + 1) ≥ 0 by nlinarith), Real.sqrt_nonneg (2)] }
      all_goals try { ring_nf <;> norm_num [Real.sq_sqrt, Real.sqrt_mul_self] <;> ring } 
      all_goals try { nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1), Real.sq_sqrt (show (2 * (k : ℝ) + 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (2 * (k + 1 : ℝ) + 1) ≥ 0 by nlinarith), Real.sqrt_nonneg (2)] }
      all_goals try { linarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1), Real.sqrt_nonneg (2 * (k + 1 : ℝ) + 1), Real.sq_sqrt (show (2 * (k : ℝ) + 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (2 * (k + 1 : ℝ) + 1) ≥ 0 by nlinarith), Real.sqrt_nonneg (2)] }
    specialize h2 n 
    simpa using h2 
  specialize h1 1009 
  norm_num at h1 ⊢ 
  linarith
  all_goals try { ring_nf <;> norm_num <;> ring }
  all_goals try { tauto }
  all_goals try { nlinarith [Real.sqrt_nonneg (2 * (1008 : ℝ) + 1), Real.sqrt_nonneg (2 * (1008 : ℝ) + 3), Real.sq_sqrt (show (2 * (1008 : ℝ) + 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (2 * (1008 : ℝ) + 3) ≥ 0 by nlinarith), Real.sqrt_nonneg (2 : ℝ)] }
  <;> try { ring_nf }
  <;> try { nlinarith }