import Mathlib

theorem algebra_247526 (t : ℝ) (h : (1 + Real.sin t) * (1 + Real.cos t) = 5 / 4) :
    Real.sin t + Real.cos t = -1 + Real.sqrt 10 / 2 := by
  have h1 : (1 + Real.sin t) * (1 + Real.cos t) = 5 / 4 := h
  have h2 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  -- First manipulate the given equation
  have h5 : (Real.sin t + Real.cos t) + (Real.sin t * Real.cos t) = 1 / 4 := by
    nlinarith [h1, h2]
  have h4 : (Real.sin t + Real.cos t) ^ 2 = Real.sin t ^ 2 + Real.cos t ^ 2 + 2 * (Real.sin t * Real.cos t) := by
    ring
  rw [show Real.sin t ^ 2 + Real.cos t ^ 2 = 1 by linarith [h2]] at h4
  have h7 : Real.sin t * Real.cos t = 1 / 4 - (Real.sin t + Real.cos t) := by 
    linarith [h5]
  -- Substitute into h4
  have h8 : (Real.sin t + Real.cos t) ^ 2 + 2 * (Real.sin t + Real.cos t) - 3 / 2 = 0 := by 
    rw [h7] at h4
    nlinarith 
  have h9 : (Real.sin t + Real.cos t - (-2 + Real.sqrt 10) / 2) * (Real.sin t + Real.cos t - (-2 - Real.sqrt 10) / 2) = 0 := by
    nlinarith [h8, Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- $\sin t + \cos t = -1 + \Real.sqrt 10 / 2$
    linarith 
  · -- $\sin t + \cos t = -1 - \Real.sqrt 10 / 2$ is impossible
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (Real.sin t - Real.cos t), sq_nonneg (Real.sin t + 1), sq_nonneg (Real.cos t + 1)]