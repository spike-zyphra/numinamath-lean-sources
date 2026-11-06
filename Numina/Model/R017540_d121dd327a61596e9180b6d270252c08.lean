import Mathlib

theorem algebra_234536 (x : ℝ) (h : Real.sin x - Real.cos x = Real.sqrt 3 / 3) :
    (Real.sin x)^6 + (Real.cos x)^6 = 2 / 3 := by

  have h1 : (Real.sin x - Real.cos x) ^ 2 = 1 / 3 := by
    rw [h]
    have h2 : (Real.sqrt 3 / 3) ^ 2 = 1 / 3 := by
      calc
        (Real.sqrt 3 / 3) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring
        _ = 3 / 9 := by rw [Real.sq_sqrt]; positivity
        _ = 1 / 3 := by norm_num
    linarith

  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h4 : (Real.sin x - Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 - 2 * (Real.sin x * Real.cos x) := by
    ring

  rw [h4] at h1
  rw [h3] at h1

  have h5 : Real.sin x * Real.cos x = 1 / 3 := by
    nlinarith

  have h6 : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) ^ 3 - 3 * ((Real.sin x) * (Real.cos x)) ^ 2 * ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) := by
    ring

  rw [h6]
  rw [h3, h5]

  all_goals norm_num