import Mathlib

theorem algebra_207800 (x y : ℝ) (h : Real.sin x - Real.sin y = 3 / 4) :
    Real.cos (x - y) ≤ 23 / 32 := by
  have h1 : (Real.sin x - Real.sin y) ^ 2 = (3 / 4) ^ 2 := by
    rw [h]

  have h4 : (Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2 = 2 - 2 * Real.cos (x - y) := by
    have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h6 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    have h7 : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
      rw [Real.cos_sub]
      all_goals ring

    calc
      (Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2
        = Real.sin x ^ 2 - 2 * Real.sin x * Real.sin y + Real.sin y ^ 2 + Real.cos x ^ 2 - 2 * Real.cos x * Real.cos y + Real.cos y ^ 2 := by ring
      _ = (Real.sin x ^ 2 + Real.cos x ^ 2) + (Real.sin y ^ 2 + Real.cos y ^ 2) - 2 * (Real.sin x * Real.sin y + Real.cos x * Real.cos y) := by ring
      _ = (1 : ℝ) + (1 : ℝ) - 2 * (Real.sin x * Real.sin y + Real.cos x * Real.cos y) := by
        rw [h5, h6]
      _ = 2 - 2 * (Real.sin x * Real.sin y + Real.cos x * Real.cos y) := by ring
      _ = 2 - 2 * Real.cos (x - y) := by
        rw [h7]
        all_goals ring

  have h5 : (Real.sin x - Real.sin y) ^ 2 = (3 / 4) ^ 2 := by
    linarith [h1]

  have h6 : (3 / 4 : ℝ) ^ 2 = (9 / 16 : ℝ) := by norm_num
  rw [h6] at h5

  nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin x - Real.sin y), Real.cos_le_one (x - y), Real.cos_le_one x, Real.cos_le_one y, sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin y - 1), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y]