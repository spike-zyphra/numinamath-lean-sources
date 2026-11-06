import Mathlib

theorem algebra_5619 {x y : ℝ} (h : abs (x + 2018) + y ^ 2 - 4034 * y + 2017 ^ 2 = 0) :
    ∑ i ∈ Finset.range 1010, (x + y) ^ (2 * i + 1) = -1010 := by

  have h1 : abs (x + 2018) ≥ 0 := abs_nonneg (x + 2018)
  have h2 : y ^ 2 - 4034 * y + 2017 ^ 2 ≥ 0 := by 
    nlinarith [sq_nonneg (y - 2017)]

  have h3 : abs (x + 2018) = 0 := by 
    linarith [h1, h2, h]

  have h4 : y ^ 2 - 4034 * y + 2017 ^ 2 = 0 := by 
    linarith [h1, h2, h]

  have hy : y = 2017 := by
    nlinarith [sq_nonneg (y - 2017)]

  have hx : x = -2018 := by
    rw [abs_eq_zero] at h3 
    linarith

  rw [hx, hy]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf <;> norm_num