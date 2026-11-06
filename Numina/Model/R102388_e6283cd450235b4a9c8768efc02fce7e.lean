import Mathlib

theorem algebra_5584 {x y : ℝ} (h : abs (x - 2010) + y ^ 2 - 4016 * y + 2008 ^ 2 = 0) :
    ∑ i ∈ Finset.range 10, (1 / (x - y) ^ (i + 1)) = 1023 / 1024 := by
  have h1 : abs (x - 2010) ≥ 0 := abs_nonneg (x - 2010)
  have h2 : y ^ 2 - 4016 * y + 2008 ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (y - 2008)]
  have h3 : abs (x - 2010) = 0 := by 
    linarith [h1, h2, h]
  have h4 : x - 2010 = 0 := abs_eq_zero.1 h3
  have hx : x = 2010 := by
    linarith
  have h5 : y ^ 2 - 4016 * y + 2008 ^ 2 = 0 := by
    linarith [h1, h2, h]
  have h6 : (y - 2008) ^ 2 = 0 := by
    nlinarith
  have h7 : y - 2008 = 0 := by 
    apply pow_eq_zero 
    exact h6
  have hy : y = 2008 := by
    linarith
  have hxy : x - y = 2 := by
    rw [hx, hy]
    norm_num
  rw [hxy]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf <;> norm_num