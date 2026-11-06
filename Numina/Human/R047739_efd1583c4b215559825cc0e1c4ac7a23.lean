import Mathlib

open Real Set
open scoped BigOperators

/- ## Problem Statement

Calculate the lengths of the arcs of the curves given by the parametric equations.


$$

\begin{aligned}
& \left\{\begin{array}{l}
x=8(\cos t+t \sin t) \\
y=8(\sin t-t \cos t)
\end{array}\right. \\
& 0 \leq t \leq \frac{\pi}{4}
\end{aligned}

$$
 -/
theorem calculus_152681 (f : ℝ → ℝ × ℝ)
  (hf : f = λ t => (8 * (cos t + t * sin t), 8 * (sin t - t * cos t))) :
  ∫ t in (0)..(π/4), Real.sqrt ((deriv f t).1^2 + (deriv f t).2^2) = (π^2)/4 := by
  rw [show deriv f = λ t ↦ (8 * t * cos t, 8 * t * sin t) from by
    -- Use the product rule for t sin t and t cos t
    have deriv_t_sin := λ x ↦ HasDerivAt.mul (hasDerivAt_id x) (hasDerivAt_sin x)
    have deriv_t_cos := λ x ↦ HasDerivAt.mul (hasDerivAt_id x) (hasDerivAt_cos x)
    -- (f + g)' = f' + g'
    have deriv_cos_plus_t_sin := λ x ↦ HasDerivAt.add (hasDerivAt_cos x) (deriv_t_sin x)
    have deriv_sin_minus_t_cos := λ x ↦ HasDerivAt.sub (hasDerivAt_sin x) (deriv_t_cos x)
    -- (cf)' = c f'
    have deriv_first := λ x ↦ HasDerivAt.const_mul (8: ℝ) (deriv_cos_plus_t_sin x)
    have deriv_second := λ x ↦ HasDerivAt.const_mul (8: ℝ) (deriv_sin_minus_t_cos x)
    -- (f, g)' = (f', g')
    have deriv_pair := λ x ↦ HasDerivAt.prod (deriv_first x) (deriv_second x)
    simp [← mul_assoc] at deriv_pair
    rw [hf]
    funext x
    exact (deriv_pair x).deriv
  ]
  simp
  calc
    ∫ t in (0)..(π/4), √((8 * t * cos t)^2 + (8 * t * sin t)^2)
      = ∫ t in (0)..(π/4), (8*t) := by
      apply intervalIntegral.integral_congr
      unfold EqOn
      intro x x_interval
      -- If x is in the interval [0, π/4], then x is nonnegative. This is needed to show that a = 8x iff a^2 = (8x)^2
      rw [mem_uIcc] at x_interval
      have x_nonneg: 0 ≤ x := by
        rcases x_interval with ⟨h, _⟩ | ⟨_, _⟩
        exact h
        linarith [pi_pos]
      beta_reduce
      apply (sq_eq_sq₀ _ _).mp
      rw [sq_sqrt]
      -- (8t cos t)^2 + (8t sin t)^2 = 64 t^2 (cos^2 t + sin^2 t) = 64 t^2
      repeat rw [mul_pow]
      rw [←mul_add, add_comm, sin_sq_add_cos_sq]
      ring
      all_goals positivity
      -- The integral of 8x is 4x^2
    _ = 8 * ∫ t in (0)..(π/4), t := by apply intervalIntegral.integral_const_mul
    _ = 8 * (((π/4)^2 - 0^2) / 2) := by rw [integral_id]
    _ = (π^2)/4 := by ring