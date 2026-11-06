import Mathlib

theorem algebra_266957 : Real.logb 2 ((∏ i ∈ Finset.range 7, (2^(2^i) + 1)) + 1) = 128 := by 
  have h1 : (∏ i ∈ Finset.range 7, (2^(2^i) + 1 : ℝ)) + 1 = (2 : ℝ) ^ (128 : ℕ) := by
    norm_num [Finset.prod_range_succ]
    <;> ring_nf <;> norm_num
  rw [h1]
  have h2 : Real.logb 2 ((2 : ℝ) ^ (128 : ℕ)) = (128 : ℝ) := by
    simp [Real.logb_eq_iff_rpow_eq]
    <;> norm_num
    all_goals linarith
  rw [h2]
  all_goals norm_num