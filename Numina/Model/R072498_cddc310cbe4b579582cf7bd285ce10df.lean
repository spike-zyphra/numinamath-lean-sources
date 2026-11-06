import Mathlib

theorem algebra_4613 {x y : ℝ} (h : 2018 * (x + y) ^ 2 = |((1 / 2) * x + (3 / 2) * y - 1)| * (-1)) : x ^ 2018 + y ^ 2018 = 2 := by
  have h1 : 2018 * (x + y) ^ 2 ≥ 0 := by
    apply mul_nonneg
    norm_num
    apply pow_two_nonneg
  have h2 : |((1 / 2) * x + (3 / 2) * y - 1)| ≥ 0 := abs_nonneg ((1 / 2) * x + (3 / 2) * y - 1)
  have h3 : |((1 / 2) * x + (3 / 2) * y - 1)| * (-1) ≤ 0 := by 
    nlinarith [abs_nonneg ((1 / 2) * x + (3 / 2) * y - 1)]
  have h4 : 2018 * (x + y) ^ 2 = 0 := by 
    linarith [h, h1, h3]
  have h5 : (x + y) ^ 2 = 0 := by
    nlinarith
  have h6 : x + y = 0 := by 
    rw [sq_eq_zero_iff] at h5
    exact h5
  have hy : y = -x := by linarith
  have h7 : |((1 / 2) * x + (3 / 2) * y - 1)| = 0 := by 
    nlinarith [h, h4, h3]
  have h8 : (1 / 2) * x + (3 / 2) * y - 1 = 0 := by 
    rwa [abs_eq_zero] at h7
  have eq1 : x = -1 := by 
    rw [hy] at h8 
    linarith
  have eq2 : y = 1 := by 
    linarith [eq1, hy]
  rw [eq1, eq2]
  norm_num