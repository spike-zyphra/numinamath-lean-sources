import Mathlib

open Real Set
open scoped BigOperators

/- 884. Find the length of the cardioid $x=2 a \cos t-a \cos 2 t, y=$ $-2 a \sin t-a \sin 2 t$. -/
theorem calculus_185933 (a : ℝ) (ha : 0 ≤ a) :
    ∫ t in (0)..(2 * π), Real.sqrt ((deriv (λ t => 2 * a * cos t - a * cos (2 * t)) t)^2 +
      (deriv (λ t => 2 * a * sin t - a * sin (2 * t)) t)^2) = 16 * a := by
  -- Show that the derivative of 2 * a * cos t - a * cos (2 * t) is
  -- 2 * a * (-sin t) - a * (-sin (2 * t) * (2 * 1)).
  have eq1 t : HasDerivAt (fun t => 2 * a * cos t - a * cos (2 * t)) (2 * a * (-sin t) - a * (-sin (2 * t) * (2 * 1))) t := by
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply hasDerivAt_cos
    · apply HasDerivAt.const_mul
      apply HasDerivAt.cos
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' t
  -- Show that the derivative of 2 * a * sin t - a * sin (2 * t) is
  -- 2 * a * cos t - a * (cos (2 * t) * (2 * 1)).
  have eq2 t : HasDerivAt (fun t => 2 * a * sin t - a * sin (2 * t)) (2 * a * cos t - a * (cos (2 * t) * (2 * 1))) t := by
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply hasDerivAt_sin
    · apply HasDerivAt.const_mul
      apply HasDerivAt.sin
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' t
  -- Prove the equality:
  -- (2 * a * (-sin t) - a * (-sin (2 * t) * (2 * 1)))^2 + (2 * a * cos t - a * (cos (2 * t) * (2 * 1)))^2
  --   = (4 * a * sin (t / 2))^2.
  have eq3 t : (2 * a * (-sin t) - a * (-sin (2 * t) * (2 * 1)))^2 + (2 * a * cos t - a * (cos (2 * t) * (2 * 1)))^2
      = (4 * a * sin (t / 2))^2 := calc
    _ = 4 * a^2 * (sin t^2 + cos t^2 + (sin (2 * t)^2 + cos (2 * t)^2) - 2 * (cos t * cos (2 * t) + sin t * sin (2 * t))) := by
      ring
    -- Simplify the original expression and get 4 * a^2 * (1 + 1 - 2 * cos t).
    _ = 4 * a^2 * (1 + 1 - 2 * cos t) := by
      congrm _ * (?_ + ?_ - 2 * ?_)
      · rw [sin_sq_add_cos_sq]
      · rw [sin_sq_add_cos_sq]
      · rw [← cos_sub, show t - 2 * t = -t by ring, cos_neg]
    -- The result follows from sin (t / 2)^2 = 1 / 2 - cos t / 2.
    _ = (4 * a * sin (t / 2))^2 := by
      ring_nf
      rw [sin_sq_eq_half_sub]
      ring_nf
  -- It is left to compute the integral of √((4 * a * sin (t / 2))^2) on [0, 2 * π].
  simp_rw [fun t => (eq1 t).deriv, fun t => (eq2 t).deriv, eq3]
  rw [intervalIntegral.integral_congr (g := fun t => 4 * a * sin (t / 2))]
  -- Compute the integral of 4 * a * sin (t / 2) on [0, 2 * π].
  · rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_div _ (by norm_num)]
    rw [integral_sin]
    simp
    ring
  -- Show that √((4 * a * sin (t / 2))^2) = 4 * a * sin (t / 2) on [0, 2 * π].
  · rw [Set.uIcc_of_le (by positivity)]
    simp only [EqOn, mem_Icc, and_imp]
    intro x hx1 hx2
    rw [sqrt_sq]
    apply mul_nonneg (by positivity)
    apply sin_nonneg_of_nonneg_of_le_pi <;> linarith