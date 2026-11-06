import Mathlib

theorem algebra_223151 (x y : ℝ) (h₀ : Real.sin x + Real.sin y = 1 / 3) (h₁ : Real.cos x - Real.cos y = 1 / 5) :
    Real.sin (x - y) = -15 / 17 ∧ Real.cos (x + y) = 208 / 225 := by
  have h4 : Real.sin y = 1 / 3 - Real.sin x := by linarith
  have h5 : Real.cos y = Real.cos x - 1 / 5 := by linarith
  have h6 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h7 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  rw [show Real.sin y = 1 / 3 - Real.sin x by linarith] at h7
  rw [show Real.cos y = Real.cos x - 1 / 5 by linarith] at h7
  have hsin : Real.sin (x - y) = -15 / 17 := by
    rw [Real.sin_sub]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, h₀, h₁, h4, h5]
  have hcos : Real.cos (x + y) = 208 / 225 := by
    rw [Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, h₀, h₁, h4, h5]
  constructor
  · exact hsin
  · exact hcos