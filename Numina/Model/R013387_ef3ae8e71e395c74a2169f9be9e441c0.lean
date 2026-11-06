import Mathlib

open Real

theorem other_47614 : ∃ N : ℤ, ∑ i ∈ Finset.range 99, ((sqrt (i + 1) + sqrt (i + 2)) ^ (-1 : ℤ) : ℝ) = N := by
  use 9
  have h1 : ∀ i : ℕ, (sqrt (i + 1) + sqrt (i + 2)) ^ (-1 : ℤ) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : ((sqrt (i + 1) + sqrt (i + 2)) : ℝ) ≠ 0 := by 
      positivity
    have h3 : ((sqrt (i + 1) + sqrt (i + 2)) ^ (-1 : ℤ) : ℝ) = 1 / (sqrt (i + 1) + sqrt (i + 2)) := by
      simp [zpow_neg_one]
    rw [h3]
    have h4 : (sqrt (i + 1) + sqrt (i + 2)) * (sqrt (i + 2) - sqrt (i + 1)) = (1 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (i + 2 : ℝ) by nlinarith), 
        sq_nonneg (sqrt (i + 2) - sqrt (i + 1)), 
        sq_nonneg (sqrt (i + 1) + sqrt (i + 2))
      ]
    field_simp [h2]
    <;> linarith
  have h2 : ∑ i in Finset.range 99, ((sqrt (i + 1) + sqrt (i + 2)) ^ (-1 : ℤ) : ℝ) = (9 : ℝ) := by 
    rw [Finset.sum_congr rfl (fun i hi => h1 i)]
    have h3 : ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1)) = (sqrt (100 : ℝ) - sqrt (1 : ℝ)) := by 
      have h4 : ∀ n : ℕ, ∑ i in Finset.range n, (sqrt (i + 2) - sqrt (i + 1)) = sqrt ((n : ℝ) + 1) - sqrt (1 : ℝ) := by
        intro n
        induction n with
        | zero => 
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp
          <;> ring_nf <;> field_simp
      specialize h4 99
      norm_num at h4 ⊢
      <;> linarith
    rw [h3]
    have h4 : sqrt (100 : ℝ) = (10 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : sqrt (1 : ℝ) = (1 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4, h5]
    all_goals norm_num
  norm_num at h2 ⊢
  linarith