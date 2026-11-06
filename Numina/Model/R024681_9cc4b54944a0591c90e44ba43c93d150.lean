import Mathlib

theorem algebra_20939 (x : ℕ → ℝ) (hx : ∀ n, x n = Real.logb n (n + 1)) :
    ∏ i ∈ Finset.Icc 4 127, x i = 7 / 2 := by

  have h1 : ∀ (i : ℕ), x i = Real.log (i + 1) / Real.log i := by
    intro i
    rw [hx i]
    simp [Real.logb]
    all_goals linarith
  have h2 : ∏ i ∈ Finset.Icc 4 127, x i = (Real.log (128 : ℝ) ) / (Real.log (4 : ℝ) ) := by
    have h3 : ∀ i ∈ Finset.Icc 4 127, x i = Real.log (i + 1) / Real.log i := by
      intro i hi
      apply h1
    norm_num [Finset.prod_Icc_succ_top, h3]
    all_goals norm_num
    all_goals linarith
    all_goals norm_num
  have h3 : Real.log (128 : ℝ) = 7 * Real.log (2 : ℝ) := by
    rw [show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h5 : Real.log (2 : ℝ) ≠ 0 := by
    have h6 : Real.log (2 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals linarith
    linarith
  rw [h2, h3, h4]
  have h6 : Real.log (2 : ℝ) ≠ 0 := by
    apply h5
  field_simp [h6]
  <;> ring_nf
  all_goals norm_num
  all_goals linarith
  all_goals norm_num
  all_goals linarith