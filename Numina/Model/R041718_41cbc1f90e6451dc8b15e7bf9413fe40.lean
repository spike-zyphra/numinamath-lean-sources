import Mathlib

open Real

theorem algebra_189962 : ∑ i ∈ Finset.range 99, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 9 := by
  have h1 : ∀ i : ℕ, 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by
      positivity
    field_simp [h2]
    have h3 : (sqrt (i + 2)) ^ 2 = (i + 2 : ℝ) := Real.sq_sqrt (by nlinarith)
    have h4 : (sqrt (i + 1)) ^ 2 = (i + 1 : ℝ) := Real.sq_sqrt (by nlinarith)
    nlinarith [Real.sqrt_nonneg (i + 2 : ℝ), Real.sqrt_nonneg (i + 1 : ℝ)]
  have h2 : ∑ i in Finset.range 99, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 
    ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1)) := by
    apply Finset.sum_congr (by rfl)
    intro i hi
    exact h1 i
  rw [h2]
  have h3 : ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1)) = sqrt (99 + 1) - sqrt (0 + 1) := by
    norm_num [Finset.sum_range_succ]
    <;> ring
  rw [h3]
  have h4 : sqrt (99 + 1 : ℝ) = (10 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : sqrt ( (0 + 1 : ℝ) ) = (1 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h4, h5]
  all_goals norm_num