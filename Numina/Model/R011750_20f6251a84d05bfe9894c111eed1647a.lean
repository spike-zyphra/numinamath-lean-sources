import Mathlib

open Real

theorem calculus_152844 (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hf : f = λ t => exp t * (cos t + sin t))
    (hg : g = λ t => exp t * (cos t - sin t)) :
    ∫ t in (Real.pi / 6)..(Real.pi / 4), Real.sqrt ((deriv f t)^2 + (deriv g t)^2) =
    2 * (exp (Real.pi / 4) - exp (Real.pi / 6)) := by
  -- First, we need to compute the derivatives of f and g.
  have f_eq : deriv f = fun t => 2 * exp t * cos t := by
    rw [hf]
    funext t
    simp [deriv_mul, differentiableAt_id', differentiableAt_exp, differentiableAt_cos, differentiableAt_sin]
    ring
  have g_eq : deriv g = fun t => -2 * exp t * sin t := by 
    rw [hg]
    funext t
    simp [deriv_mul, differentiableAt_id', differentiableAt_exp, differentiableAt_cos, differentiableAt_sin]
    ring
  -- Show that sqrt((f')² + (g')²) = 2e^t
  have h1 : ∀ t, Real.sqrt ((deriv f t)^2 + (deriv g t)^2) = 2 * exp t := by
    intro t
    rw [f_eq, g_eq]
    have h2 : (2 * exp t * cos t)^2 + (-2 * exp t * sin t)^2 = 4 * (exp t)^2 := by
      calc
        (2 * exp t * cos t)^2 + (-2 * exp t * sin t)^2
          = 4 * (exp t)^2 * (cos t)^2 + 4 * (exp t)^2 * (sin t)^2 := by ring
        _ = 4 * (exp t)^2 * ((cos t)^2 + (sin t)^2) := by ring 
        _ = 4 * (exp t)^2 * 1 := by rw [Real.cos_sq_add_sin_sq t]
        _ = 4 * (exp t)^2 := by ring
    -- Therefore sqrt(4e^2t) = 2e^t.
    have h3 : Real.sqrt (4 * (exp t)^2) = 2 * exp t := by
      have h4 : Real.sqrt (4 * (exp t)^2) = Real.sqrt (4) * Real.sqrt ((exp t)^2) := by 
        rw [Real.sqrt_mul (by positivity)]
      have h5 : Real.sqrt (4 : ℝ) = 2 := by 
        rw [Real.sqrt_eq_cases]
        norm_num
      have h6 : Real.sqrt ((exp t)^2) = exp t := by
        rw [Real.sqrt_sq (by positivity)]
      rw [h4, h5, h6]
      all_goals linarith
    rw [h2]
    exact h3
  -- Compute integral that sqrt term is 2e^t.
  simp_rw [h1]
  simp [intervalIntegral.integral_const, mul_comm]
  all_goals ring