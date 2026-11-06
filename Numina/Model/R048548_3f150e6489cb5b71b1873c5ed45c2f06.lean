import Mathlib

theorem algebra_4981 {x y : ℝ} (h : abs (x - 2022) + (y + 2023)^2 = 0) :
    ∑ i ∈ Finset.range 2021, (x + y)^(i + 1) = -1 := by 
  have h1 : abs (x - 2022) = 0 := by 
    linarith [abs_nonneg (x - 2022), sq_nonneg (y + 2023)]
  have hx : x = 2022 := by
    rw [abs_eq_zero] at h1
    linarith
  have h2 : (y + 2023) ^ 2 = 0 := by
    linarith [abs_nonneg (x - 2022), sq_nonneg (y + 2023)]
  have hy : y = -2023 := by
    have h3 : y + 2023 = 0 := by 
      rw [sq_eq_zero_iff] at h2
      linarith
    linarith
  have hxy : x + y = -1 := by 
    rw [hx, hy]
    norm_num
  rw [hxy]
  norm_num [Finset.sum_range_succ]