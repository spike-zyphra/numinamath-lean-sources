import Mathlib

theorem algebra_11916 {s : ℝ} (hs : s > 0) (h : 2 * s^2 = (10 * Real.sqrt 2)^2) :
    s^2 = 100 := by
  have h1 : (10 * Real.sqrt 2) ^ 2 = 200 := by
    calc
      (10 * Real.sqrt 2) ^ 2 = 10^2 * (Real.sqrt 2)^2 := by ring
      _ = 100 * (Real.sqrt 2)^2 := by norm_num
      _ = 100 * 2 := by rw [Real.sq_sqrt]; positivity
      _ = 200 := by norm_num
  rw [h1] at h
  linarith