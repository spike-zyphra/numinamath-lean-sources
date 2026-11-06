import Mathlib

theorem algebra_5733 {x y : ℝ} (h : abs (x - 2018) + (y + 2017) ^ 2 = 0) :
    ∑ i ∈ Finset.Icc 1 2018, (x + y) ^ i = 2018 := by
  have h1 : abs (x - 2018) = 0 := by
    linarith [abs_nonneg (x - 2018), sq_nonneg (y + 2017)]
  have h2 : (y + 2017) ^ 2 = 0 := by
    linarith [abs_nonneg (x - 2018), sq_nonneg (y + 2017)]
  have hx : x = 2018 := by
    rw [abs_eq_zero] at h1
    linarith
  have hy : y = -2017 := by
    have h3 : y + 2017 = 0 := by
      apply pow_eq_zero 
      exact h2
    linarith
  have hxy : x + y = 1 := by
    rw [hx, hy]
    norm_num
  rw [hxy]
  norm_num [Finset.sum_Icc_succ_top]