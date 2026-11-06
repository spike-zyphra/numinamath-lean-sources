import Mathlib

open Real

theorem algebra_134872 (a : ℕ → ℝ)
    (ha : ∀ n, a n = 1 / ((n + 1) * sqrt n + n * sqrt (n + 1))) :
    ∑ i in Finset.Icc 1 99, a i = 9 / 10 := by

  have h1 : ∀ n : ℕ, n ≥ 1 → a n = (1 / sqrt (↑n : ℝ)) - (1 / sqrt ((↑n + 1 : ℝ))) := by
    intro n hn
    have h2 : a n = 1 / ((↑n + 1) * sqrt (↑n : ℝ) + (↑n) * sqrt ((↑n + 1 : ℝ))) := by
      specialize ha n
      simpa using ha
    rw [h2]
    have h3 : (↑n : ℝ) ≥ 0 := by
      positivity
    have h4 : ((↑n + 1 : ℝ)) ≥ 0 := by
      positivity
    have h11 : sqrt (↑n : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      have h12 : (↑n : ℝ) > 0 := by
        have h0 : (↑n : ℝ) ≥ (1 : ℝ) := by
          exact_mod_cast (show n ≥ 1 by linarith)
        linarith
      linarith
    have h13 : sqrt ((↑n + 1 : ℝ)) > 0 := by
      apply Real.sqrt_pos.mpr
      have h14 : (↑n + 1 : ℝ) > 0 := by
        have h0 : (↑n : ℝ) ≥ (1 : ℝ) := by
          exact_mod_cast (show n ≥ 1 by linarith)
        linarith
      linarith
    field_simp [h11, h13]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ ↑n by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ ↑n + 1 by positivity), 
          mul_nonneg (Real.sqrt_nonneg (↑n : ℝ)) (Real.sqrt_nonneg (↑n + 1 : ℝ)), 
          sq_nonneg (sqrt (↑n : ℝ) - sqrt ((↑n + 1 : ℝ))), 
          Real.sqrt_nonneg (↑n : ℝ), 
          Real.sqrt_nonneg (↑n + 1 : ℝ)]
  
  have h2 : ∀ (k : ℕ), ∑ i in Finset.Icc 1 k, a i = 1 - (1 / sqrt ((↑k + 1 : ℝ))) := by
    intro k
    induction k with
    | zero =>
      norm_num [Finset.sum_eq_zero]
      all_goals
      try { linarith }
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h10 : a (k + 1) = (1 / sqrt ((↑(k + 1) : ℝ))) - (1 / sqrt ((↑(k + 1) + 1 : ℝ))) := by
        have h90 : (k + 1 : ℕ) ≥ 1 := by linarith
        specialize h1 (k + 1) h90
        simpa using h1
      rw [h10]
      field_simp [Real.sqrt_nonneg ((↑k + 1 + 1 : ℝ)), Real.sqrt_nonneg ((↑k + 1 : ℝ)), show (↑k + 1 : ℝ) ≥ 0 by positivity, show (↑k + 1 + 1 : ℝ) ≥ 0 by positivity]
      all_goals
      ring_nf
  
  specialize h2 99
  norm_num at h2 ⊢
  have h30 : sqrt (100 : ℝ) = 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  rw [h30] at h2
  linarith