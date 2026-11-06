import Mathlib

theorem algebra_13472 (x : ℝ) (h : Real.tan x = Real.sqrt 7 / 3) : 1 - Real.cos (2 * x) = 7 / 8 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at h
  have h1 : Real.cos x ≠ 0 := by
    by_contra h2
    rw [h2] at h
    field_simp at h
    all_goals nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]

  have h2 : Real.sin x = Real.sqrt 7 / 3 * Real.cos x := by
    field_simp [h1] at h
    linarith
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h4 : Real.sin x ^ 2 = (7 / 9) * Real.cos x ^ 2 := by
    rw [h2]
    have h5 : (Real.sqrt 7 / 3 * Real.cos x) ^ 2 = (7 / 9) * Real.cos x ^ 2 := by
      calc
        (Real.sqrt 7 / 3 * Real.cos x) ^ 2
          = (Real.sqrt 7 / 3) ^ 2 * Real.cos x ^ 2 := by ring
        _ = ( (Real.sqrt 7) ^ 2 / 9 ) * Real.cos x ^ 2 := by ring
        _ = ( 7 / 9 ) * Real.cos x ^ 2 := by
          have h7 : (Real.sqrt 7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
          rw [h7]
    linarith [h5]

  have h5 : Real.cos x ^ 2 = 9 / 16 := by
    have h6 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := h3
    rw [h4] at h6
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (Real.cos x * 3), sq_nonneg (Real.cos x) ]

  have h6 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
    rw [Real.cos_two_mul]

  rw [h6, h5]
  norm_num