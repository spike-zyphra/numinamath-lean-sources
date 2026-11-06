import Mathlib

open Real

theorem algebra_119839 (a : ℕ → ℝ)
    (ha : ∀ n, a n = 1 / ((n + 1) * sqrt n + n * sqrt (n + 1))) :
    ∑ k in Finset.Icc 1 99, a k = 9 / 10 := by
  refine' (by
    -- define $a_n$.
    have h2 : ∀ n : ℕ, a n = 1 / ((↑n + 1) * sqrt (↑n : ℝ) + ↑n * sqrt (↑n + 1 : ℝ)) := by 
      intro n 
      exact_mod_cast ha n 
    have h3 : ∀ n > 0, a n = 1 / sqrt (↑n : ℝ) - 1 / sqrt (↑n + 1 : ℝ) := by
      intro n hn 
      rw [h2 n] 
      have h4 : (↑n : ℝ) > 0 := by exact_mod_cast hn 
      have h5 : (↑n + 1 : ℝ) > 0 := by 
        linarith 
      have h6 : ((↑n + 1 : ℝ) * sqrt (↑n : ℝ) + (↑n : ℝ) * sqrt (↑n + 1 : ℝ)) ≠ 0 := by 
        have h7 : (↑n + 1 : ℝ) * sqrt (↑n : ℝ) > 0 := by 
          apply mul_pos 
          have h9 : (↑n + 1 : ℝ) > 0 := by linarith 
          positivity 
          have h10 : sqrt (↑n : ℝ) > 0 := by 
            apply Real.sqrt_pos.mpr 
            positivity 
          positivity 
        have h8 : (↑n : ℝ) * sqrt (↑n + 1 : ℝ) ≥ 0 := by 
          apply mul_nonneg 
          positivity 
          have h9 : sqrt (↑n + 1 : ℝ) ≥ 0 := by 
            apply Real.sqrt_nonneg 
          positivity 
        have h7 : (↑n + 1 : ℝ) * sqrt (↑n : ℝ) + (↑n : ℝ) * sqrt (↑n + 1 : ℝ) > 0 := by 
          linarith 
        positivity 
      field_simp [h6, sqrt_pos.mpr h4, sqrt_pos.mpr h5, Real.sq_sqrt] 
      <;> ring_nf <;> field_simp [sqrt_pos.mpr h4, sqrt_pos.mpr h5, Real.sq_sqrt]
      <;> ring_nf <;> norm_num 
      <;> ring_nf 
      <;> norm_num [Real.sq_sqrt] 
      all_goals linarith [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ)]
      all_goals ring_nf <;> norm_num 
      all_goals linarith 
      all_goals simp 
      all_goals linarith 
      all_goals norm_num 
      all_goals linarith [Real.sq_sqrt (show (↑n : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (↑n + 1 : ℝ) ≥ 0 by linarith)]
      <;> ring_nf <;> norm_num 
      all_goals linarith [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ)]
      all_goals ring_nf <;> norm_num 
      all_goals linarith 
    -- use Finset.sum_Icc_succ_top to handle the total sum.
    norm_num [Finset.sum_Icc_succ_top, h3] 
    <;> norm_num 
    have h5 : sqrt (100 : ℝ) = 10 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      all_goals norm_num 
    rw [h5] 
    <;> norm_num 
    <;> ring_nf 
    <;> norm_num 
  ) <;> norm_num [ha]
  all_goals norm_num [ha]
  <;> try { ring }
  all_goals norm_num
  <;> try { linarith }
  all_goals norm_num
  <;> try { ring }
  all_goals norm_num
  <;> try { linarith }
  all_goals norm_num