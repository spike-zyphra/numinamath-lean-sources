import Mathlib

open Real

theorem algebra_292518 (U : ℕ → ℝ)
    (hU : ∀ n, U n = (2 * n + 1 - 2 * sqrt (n * (n + 1))) / (sqrt (n + 1) - sqrt n)) :
    (∑ i in Finset.Icc 0 41, U i) ^ 2 = 42 := by
  have h1 : ∀ n : ℕ, U n = sqrt (n + 1) - sqrt n := by
    intro n
    rw [hU n]
    by_cases h2 : n = 0
    · -- n = 0, so we have $1$
      rw [h2]
      have h1 : sqrt (0 : ℝ) = 0 := by
        simp [sqrt_eq_zero]
      have h2 : sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      simp [h1, h2]
      <;> norm_num
    · -- n > 0
      have hn : n > 0 := by omega
      have h3 : sqrt (n + 1 : ℝ) - sqrt (n : ℝ) ≠ 0 := by
        have h4 : sqrt (n + 1 : ℝ) > sqrt (n : ℝ) := by
          apply Real.sqrt_lt_sqrt
          · -- Show n ≥ 0
            have hn0 : (n : ℝ) ≥ (0 : ℝ) := by
              have hn' : n ≥ 1 := by omega
              have hn0' : (n : ℝ) ≥ (1 : ℝ) := by
                exact_mod_cast hn'
              linarith
            linarith
          · -- Show n + 1 > n
            have hn' : (n : ℝ) ≥ (0 : ℝ) := by
              have hn' : n ≥ 1 := by omega
              have hn0' : (n : ℝ) ≥ (1 : ℝ) := by
                exact_mod_cast hn'
              linarith
            nlinarith
        have h5 : sqrt (n + 1 : ℝ) - sqrt (n : ℝ) > 0 := by linarith
        linarith
      have h4 : (2 * n + 1 - 2 * sqrt ((n : ℝ) * (n + 1 : ℝ)) ) / (sqrt (n + 1 : ℝ) - sqrt (n : ℝ)) = sqrt (n + 1 : ℝ) - sqrt (n : ℝ) := by
        have h5 : sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := by
          rw [Real.sq_sqrt]
          have hn0 : (n : ℝ) ≥ (0 : ℝ) := by
            have hn' : n ≥ 1 := by omega
            have hn0' : (n : ℝ) ≥ (1 : ℝ) := by
              exact_mod_cast hn'
            linarith
          nlinarith
        have h6 : sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
          rw [Real.sq_sqrt]
          have hn0 : (n : ℝ) ≥ (0 : ℝ) := by
            have hn' : n ≥ 1 := by omega
            have hn0' : (n : ℝ) ≥ (1 : ℝ) := by
              exact_mod_cast hn'
            linarith
          nlinarith
        have h7 : sqrt (n * (n + 1 : ℝ)) = (sqrt (n : ℝ) * sqrt (n + 1 : ℝ)) := by
          have h8 : (n * (n + 1 : ℝ)) = (n : ℝ) * (n + 1 : ℝ) := by ring
          rw [h8]
          rw [← Real.sqrt_mul (by
            have hn0 : (n : ℝ) ≥ (0 : ℝ) := by
              have hn' : n ≥ 1 := by omega
              have hn0' : (n : ℝ) ≥ (1 : ℝ) := by
                exact_mod_cast hn'
              linarith
            linarith
          )]
        have h8 : (sqrt (n + 1 : ℝ) - sqrt (n : ℝ)) * (sqrt (n + 1 : ℝ) + sqrt (n : ℝ)) = 1 := by
          have h9 : (sqrt (n + 1 : ℝ) - sqrt (n : ℝ)) * (sqrt (n + 1 : ℝ) + sqrt (n : ℝ)) = (sqrt (n + 1 : ℝ) ^ 2 - sqrt (n : ℝ) ^ 2) := by
            ring
          rw [h9]
          have h10 : sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := h5
          have h11 : sqrt (n : ℝ) ^ 2 = (n : ℝ) := h6
          rw [h10, h11]
          all_goals linarith
        field_simp [h3, h8]
        nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ), Real.sq_sqrt (show (n : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (n + 1 : ℝ) ≥ 0 by nlinarith), mul_self_nonneg (sqrt (n + 1 : ℝ) - sqrt (n : ℝ)), mul_self_nonneg (sqrt (n + 1 : ℝ) + sqrt (n : ℝ)), h5, h6, h7]
      linarith
  have h3 : (∑ i in Finset.Icc 0 41, U i) = Real.sqrt 42 := by
    have h4 : ∀ i : ℕ, i ∈ Finset.Icc (0 : ℕ) 41 → U i = Real.sqrt (i + 1) - Real.sqrt (i : ℝ) := by
      intro i hi
      specialize h1 i
      simpa using h1
    rw [Finset.sum_congr rfl (fun i hi => h4 i hi)]
    have h6 : ∑ i in Finset.Icc (0 : ℕ) 41, (Real.sqrt (i + 1) - Real.sqrt (i : ℝ)) = Real.sqrt 42 := by
      norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ]
      <;> ring_nf
    linarith [h6]
  rw [h3]
  have h4 : (Real.sqrt 42) ^ 2 = (42 : ℝ) := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  linarith [h4]