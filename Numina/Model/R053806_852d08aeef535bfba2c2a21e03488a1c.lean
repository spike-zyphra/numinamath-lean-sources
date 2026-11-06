import Mathlib

theorem algebra_316589 (x : ℝ) (h : Real.sin x + Real.cos x = Real.sqrt 2 / 2) :
    (Real.sin x)^3 + (Real.cos x)^3 = 5 * Real.sqrt 2 / 8 := by
  have h2 : (Real.sin x + Real.cos x)^2 = 1/2 := by
    rw [h]
    have h3 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      calc
        (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
        _ = 2 / 4 := by rw [Real.sq_sqrt]; positivity
        _ = 1 / 2 := by norm_num
    linarith
  have h3 : (Real.sin x + Real.cos x)^2 = (Real.sin x)^2 + (Real.cos x)^2 + 2 * (Real.sin x * Real.cos x) := by
    ring
  have h4 : (Real.sin x)^2 + (Real.cos x)^2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h5 : Real.sin x * Real.cos x = -1 / 4 := by
    nlinarith [h2, h3, h4]
  have h6 : (Real.sin x)^3 + (Real.cos x)^3 = (Real.sin x + Real.cos x)^3 - 3 * (Real.sin x + Real.cos x) * (Real.sin x * Real.cos x) := by
    ring
  rw [h6, h, h5]
  have h7 : (Real.sqrt 2 / 2)^3 = Real.sqrt 2 / 4 := by
    calc
      (Real.sqrt 2 / 2) ^ 3 = (Real.sqrt 2)^3 / 8 := by ring
      _ = (Real.sqrt 2 * (Real.sqrt 2)^2)/8 := by ring
      _ = (Real.sqrt 2 * 2)/8 := by rw [Real.sq_sqrt]; positivity
      _ = Real.sqrt 2 / 4 := by ring
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h7]