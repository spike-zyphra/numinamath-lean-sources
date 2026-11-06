import Mathlib

open Real

theorem algebra_140494 : ∑ i ∈ Finset.range 99, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 9 := by
  have h1 : ∀ i : ℕ, 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by
      positivity
    have h3 : sqrt (i + 2) ^ 2 - sqrt (i + 1) ^ 2 = (i + 2 : ℝ) - (i + 1 : ℝ) := by
      have h4 : sqrt (i + 2) ^ 2 = (i + 2 : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      have h5 : sqrt (i + 1) ^ 2 = (i + 1 : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      linarith [h4, h5]
    field_simp [h2]
    <;> nlinarith [Real.sqrt_nonneg (i + 1 : ℝ), Real.sqrt_nonneg (i + 2 : ℝ),
              Real.sq_sqrt (show (0 : ℝ) ≤ i + 1 by linarith),
              Real.sq_sqrt (show (0 : ℝ) ≤ i + 2 by linarith)]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  have h8 : ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1)) = sqrt (100 : ℝ) - sqrt (1 : ℝ) := by
    norm_num [Finset.sum_range_succ]
    <;> ring
  rw [h8]
  have h9 : sqrt (100 : ℝ) = (10 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h10 : sqrt (1 : ℝ) = (1 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h9, h10]
  all_goals norm_num
  <;> ring