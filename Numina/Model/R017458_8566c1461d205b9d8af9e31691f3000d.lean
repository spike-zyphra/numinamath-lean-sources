import Mathlib

theorem algebra_196760 (x : ℕ → ℝ) (hx1 : x 1 = 2001) (hxn : ∀ n > 1, x n = n / x (n - 1))
    (a : ℝ) (ha : ∏ i ∈ Finset.Icc 1 10, x i = a) : a = 3840 := by

  have h1 : x 1 = 2001 := hx1

  have h2 : x 2 = 2 / x 1 := by
    specialize hxn 2 (by norm_num)
    simpa using hxn

  rw [h1] at h2

  have h3 : x 3 = 3 / x 2 := by
    specialize hxn 3 (by norm_num)
    simpa using hxn

  rw [h2] at h3

  have h4 : x 4 = 4 / x 3 := by
    specialize hxn 4 (by norm_num)
    simpa using hxn

  rw [h3] at h4

  have h5 : x 5 = 5 / x 4 := by
    specialize hxn 5 (by norm_num)
    simpa using hxn

  rw [h4] at h5

  have h6 : x 6 = 6 / x 5 := by
    specialize hxn 6 (by norm_num)
    simpa using hxn

  rw [h5] at h6

  have h7 : x 7 = 7 / x 6 := by
    specialize hxn 7 (by norm_num)
    simpa using hxn

  rw [h6] at h7

  have h8 : x 8 = 8 / x 7 := by
    specialize hxn 8 (by norm_num)
    simpa using hxn

  rw [h7] at h8

  have h9 : x 9 = 9 / x 8 := by
    specialize hxn 9 (by norm_num)
    simpa using hxn

  rw [h8] at h9

  have h10 : x 10 = 10 / x 9 := by
    specialize hxn 10 (by norm_num)
    simpa using hxn

  rw [h9] at h10

  have h11 : ∏ i in Finset.Icc 1 10, x i = x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * x 7 * x 8 * x 9 * x 10 := by
    simp [Finset.prod_Icc_succ_top, mul_comm]

  have h12 : x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * x 7 * x 8 * x 9 * x 10 = 3840 := by
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    norm_num

  rw [h11] at ha

  linarith [h12, ha]