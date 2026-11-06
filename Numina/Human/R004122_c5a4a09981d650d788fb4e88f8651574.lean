import Mathlib

open Real Set
open scoped BigOperators

/- 5. If the function $f(x)=\lg \left(\sin ^{6} x+\cos ^{6} x+a \sin x \cos x\right)$ has the domain $\mathbf{R}$, then the range of the real number $a$ is $\qquad$ . -/
theorem algebra_238673 (a : ℝ):
  (∀ x, sin x ^ 6 + cos x ^ 6 + a * sin x * cos x > 0) ↔ a ∈ Ioo (-1/2) (1/2) := by
  have h_inv_sqrt_two_pow_six: (√2/2)^6 = (1: ℝ)/8 := by calc
    (√2/2)^6 = ((√2)^2)^3 / 64 := by rw [div_pow]; ring
    _ = (2: ℝ)^3 / 64 := by rw [sq_sqrt]; norm_num
    _ = (1: ℝ)/8 := by norm_num
  constructor
  · intro h_trig
    -- The inequality must hold when x = π/4 so that t = 2 sin(x) cos(x) = 1. Thus -1/2 < a
    have h_lower_bound:= h_trig (π/4)
    field_simp [h_inv_sqrt_two_pow_six] at h_lower_bound
    nth_rewrite 2 [mul_assoc] at h_lower_bound
    rw [mul_self_sqrt] at h_lower_bound
    replace h_lower_bound: -(1: ℝ)/2 < a := by linarith
    -- The inequality must hold when x = -π/4 so that 2t = sin(x) cos(x) = -1. Thus a < 1/2
    have h_upper_bound := h_trig (-(π/4))
    norm_num at h_upper_bound
    rw [Even.neg_pow] at h_upper_bound
    field_simp [h_inv_sqrt_two_pow_six] at h_upper_bound
    rw [mul_assoc, mul_self_sqrt] at h_upper_bound
    replace h_upper_bound: a < (1: ℝ)/2 := by linarith
    exact mem_Ioo.mpr ⟨h_lower_bound, h_upper_bound⟩
    -- decide is used to establish that 6 is even so that (-√2/2)^6 = (√2/2)^6
    norm_num; decide; norm_num
  · rintro ⟨h_lower_bound, h_upper_bound⟩ x
    -- Let t = 2 sin(x) cos(x)
    let t := 2 * sin x * cos x
    suffices h_t: -3*t^2 + 2*a*t + 4 > 0
    -- We rewrite the expression under the logarithm as (-3t^2 + 2at + 4)/4. This must be positive.
    calc
      sin x^6 + cos x^6 + a*sin x*cos x = (sin x^2 + cos x^2) * (sin x^4 - sin x^2 * cos x^2 + cos x^4) + a*sin x*cos x := by ring
      _ = sin x^4 - sin x^2 * cos x^2 + cos x^4 + a*sin x*cos x := by rw [sin_sq_add_cos_sq, one_mul]
      _ = (sin x^2 + cos x^2)^2 - 3*sin x^2 * cos x^2 + a*sin x*cos x := by ring
      _ = (-3*t^2 + 2*a*t + 4)/4 := by rw [sin_sq_add_cos_sq]; ring
      _ > 0 := by positivity
    -- Since 3t^2 - 4 < -1, it is enough to show that at > -1/2
    suffices h_t: a*t > -(1: ℝ)/2
    have: t^2 ≤ 1 := by unfold t; rw [← sin_two_mul]; exact sin_sq_le_one (2 * x)
    linarith
    -- When a ≥ 0, multiplying t ≥ -1 by a gives us at ≥ -a > -1/2
    by_cases h_a: a ≥ 0
    have: t ≥ -1 := by unfold t; rw [← sin_two_mul]; exact neg_one_le_sin (2 * x)
    nlinarith
    -- When a < 0, multiplying t ≤ 1 by a gives us at ≥ a > -1/2
    replace h_a: a < 0 := lt_of_not_ge h_a
    have t_upper: t ≤ 1 := by unfold t; rw [← sin_two_mul]; exact sin_le_one (2 * x)
    have := (mul_le_mul_left_of_neg h_a).mpr t_upper
    linarith