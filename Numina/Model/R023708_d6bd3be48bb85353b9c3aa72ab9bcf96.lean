import Mathlib

open Real

theorem inequalities_242682 : ∑ k ∈ Finset.range 2014, logb 2 (1 + 1 / (k + 1)) < 11 := by
  have h1 : ∀ n : ℕ, ∑ k in Finset.range n, logb 2 (1 + 1 / (k + 1)) = logb 2 (n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_range_succ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [logb_div]
      all_goals ring_nf
  have h10 : ∑ k in Finset.range 2014, logb 2 (1 + 1 / (k + 1)) = logb 2 (2015 : ℝ) := by
    specialize h1 2014
    norm_num at h1 ⊢
    linarith
  rw [h10]
  have h2 : logb 2 (2015 : ℝ) < 11 := by
    have h3 : logb 2 (2015 : ℝ) < (11 : ℝ) := by
      have h5 : logb 2 (2015 : ℝ) < logb 2 (2048 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h6 : logb 2 (2048 : ℝ) = 11 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      linarith 
    linarith
  linarith