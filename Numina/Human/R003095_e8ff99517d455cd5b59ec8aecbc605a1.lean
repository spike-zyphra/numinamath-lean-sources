import Mathlib

open Real Set

/- ## Problem Statement

Calculate the lengths of the arcs of the curves given by the parametric equations.
$$
\begin{aligned}
& \left\{\begin{array}{l}
x=2(\cos t+t \sin t) \\
y=2(\sin t-t \cos t)
\end{array}\right. \\
& 0 \leq t \leq \frac{\pi}{2}
\end{aligned}
$$
 -/
theorem calculus_152795 (f : ℝ → ℝ × ℝ)
    (hf : f = λ t => (2 * (cos t + t * sin t), 2 * (sin t - t * cos t))) :
    ∫ t in (0)..(π/2), Real.sqrt ((deriv f t).1^2 + (deriv f t).2^2) = (π^2)/4 := by
  -- Show that the derivative of f(t) is
  -- (2 * (-sin t + (1 * sin t + t * cos t)), 2 * (cos t - (1 * cos t + t * (-sin t)))).
  have hd t : HasDerivAt f (2 * (-sin t + (1 * sin t + t * cos t)), 2 * (cos t - (1 * cos t + t * (-sin t)))) t := by
    rw [hf]
    apply HasDerivAt.prod <;> apply HasDerivAt.const_mul <;> apply HasDerivAt.add
    · apply hasDerivAt_cos
    · apply HasDerivAt.mul (hasDerivAt_id' _) (hasDerivAt_sin _)
    · apply hasDerivAt_sin
    · apply HasDerivAt.neg
      apply HasDerivAt.mul (hasDerivAt_id' _) (hasDerivAt_cos _)
  simp [fun t => (hd t).deriv]
  -- It is enough to show that √((2 * (t * cos t))^2 + (2 * (t * sin t))^2) = 2 * t.
  rw [intervalIntegral.integral_congr (g := fun t => 2 * t)]
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simp [EqOn, uIcc_of_le (show 0 ≤ π / 2 by linarith [pi_pos])]
  intro x hx1 hx2
  -- Square both sides of the equality.
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  rw [sq_sqrt (by positivity)]
  -- The result follows from cos x^2 + sin x^2 = 1.
  linear_combination (2 * x)^2 * (cos_sq_add_sin_sq x)