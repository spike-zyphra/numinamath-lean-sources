import Mathlib

theorem algebra_319649 (θ : ℝ) (x : ℝ) (h₁ : Real.sin (2 * x) = (Real.sin θ + Real.cos θ) / 2)
    (h₂ : (Real.cos x)^2 = Real.sin θ * Real.cos θ) :
    Real.cos (2 * x) = (-1 - Real.sqrt 33) / 8 := by 
  have eq1 : Real.sin θ + Real.cos θ = 2 * Real.sin (2 * x) := by 
    linarith [h₁]
  have eq2 : (Real.sin θ + Real.cos θ) ^ 2 = (2 * Real.sin (2 * x)) ^ 2 := by 
    rw [eq1]
  have eq3 : (Real.sin θ + Real.cos θ) ^ 2 = 1 + 2 * (Real.sin θ * Real.cos θ) := by
    calc
      (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * (Real.sin θ * Real.cos θ) := by ring
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) + 2 * (Real.sin θ * Real.cos θ) := by ring
      _ = 1 + 2 * (Real.sin θ * Real.cos θ) := by 
        have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        rw [h3]
  have eq4 : (2 * Real.sin (2 * x)) ^ 2 = 4 * (Real.sin (2 * x) ^ 2) := by ring
  rw [eq3] at eq2
  rw [eq4] at eq2 
  have h₃ : Real.cos (2 * x) = 2 * (Real.cos x)^2 - 1 := by 
    rw [Real.cos_two_mul]
  have h₄ : Real.cos (2 * x) = 2 * (Real.sin θ * Real.cos θ) - 1 := by 
    rw [h₃]
    nlinarith [h₂]
  have h5 : Real.sin θ * Real.cos θ = 2 * (Real.sin (2 * x)) ^ 2 - 1 / 2 := by 
    nlinarith [eq2, Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq x, Real.sin_two_mul x]
  have h6 : Real.cos (2 * x) = 4 * (Real.sin (2 * x)) ^ 2 - 2 := by 
    nlinarith [h₄, h5]
  have h7 : (Real.sin (2 * x)) ^ 2 = 1 - (Real.cos (2 * x)) ^ 2 := by 
    have h8 : Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * x)
    linarith
  rw [h7] at h6 
  have h8 : 4 * (Real.cos (2 * x)) ^ 2 + Real.cos (2 * x) - 2 = 0 := by 
    nlinarith [h6]
  have h9 : (Real.cos (2 * x) - (-1 + Real.sqrt 33) / 8) * (Real.cos (2 * x) - (-1 - Real.sqrt 33) / 8) = 0 := by 
    nlinarith [h8, Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- Case where $\cos 2x = \frac{-1 + \sqrt{33}}{8}$
    have hcos : Real.cos (2 * x) = (-1 + Real.sqrt 33) / 8 := by linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num), 
              Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq θ, 
              Real.sin_sq_add_cos_sq x, Real.sin_two_mul x, Real.sin_two_mul θ]
  · -- Case where $\cos 2x = \frac{-1 - \sqrt{33}}{8}$
    have hcos : Real.cos (2 * x) = (-1 - Real.sqrt 33) / 8 := by linarith
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num), 
              Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq θ, 
              Real.sin_sq_add_cos_sq x, Real.sin_two_mul x, Real.sin_two_mul θ]