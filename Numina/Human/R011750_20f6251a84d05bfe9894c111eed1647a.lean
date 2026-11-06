import Mathlib

open Real

/- ## Problem Statement

Calculate the lengths of the arcs of the curves given by the parametric equations.


$$

\begin{aligned}
& \left\{\begin{array}{l}
x=e^{t}(\cos t+\sin t) \\
y=e^{t}(\cos t-\sin t)
\end{array}\right. \\
& \frac{\pi}{6} \leq t \leq \frac{\pi}{4}
\end{aligned}

$$
 -/
theorem calculus_152844 (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hf : f = λ t => exp t * (cos t + sin t))
    (hg : g = λ t => exp t * (cos t - sin t)) :
    ∫ t in (Real.pi / 6)..(Real.pi / 4), Real.sqrt ((deriv f t)^2 + (deriv g t)^2) =
    2 * (exp (Real.pi / 4) - exp (Real.pi / 6)) := by
  -- Show that the derivative of f is 2 * exp(t) * cos(t).
  have eq1 t : deriv f t = 2 * exp t * cos t := by
    simp [hf]
    ring
  -- Show that the derivative of g is -2 * exp(t) * sin(t).
  have eq2 t : deriv g t = -2 * exp t * sin t := by
    simp [hg]
    ring
  -- Show that the integral is equal to
  -- ∫ t in (Real.pi / 6)..(Real.pi / 4), (2 * exp t).
  rw [intervalIntegral.integral_congr (g := fun t => 2 * exp t)]
  · simp
  -- It is enough to show that √(deriv  f x ^ 2 + deriv g x ^ 2) = 2 * exp(x).
  intro x hx
  calc
    -- We have
    -- deriv f x ^ 2 + deriv g x ^ 2 = (2 * exp x)^2 * (cos x^2 + sin x^2)
    --    = (2 * exp x)^2 * 1.
    √(deriv  f x ^ 2 + deriv g x ^ 2) = √((2 * exp x)^2 * (cos x ^ 2 + sin x ^ 2)) := by
      congr
      rw [eq1, eq2]
      ring
    -- √((2 * exp x)^2) = 2 * exp x since 2 * exp x > 0 for all x.
    _ = 2 * exp x := by
      simp
      rw [sqrt_sq (by positivity)]