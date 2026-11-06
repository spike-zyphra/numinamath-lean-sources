import Mathlib

theorem algebra_3271 (n m: ℕ) (h1 : n * 23 = m* 32) (h2 : n = m + 9) : (m * 32: ℝ) / 100 = 7.36 := by
  rw [h2] at h1
  have hm : m = 23 := by
    omega

  have h : (m : ℝ) = 23 := by
    exact_mod_cast hm

  rw [h]
  norm_num