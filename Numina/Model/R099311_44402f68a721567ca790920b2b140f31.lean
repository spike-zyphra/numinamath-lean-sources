import Mathlib

open Real

theorem calculus_178127 (f : ℝ → ℝ) (hf : f = fun x => exp (3 * x) * log (1 + x ^ 2)) :
    deriv f 0 = 0 := by
  rw [hf]
  -- Applying the derivative of product rule
  -- If $f(x) = u(x) \cdot v(x)$, then $f'(x) = u'(x) \cdot v(x) + u(x) \cdot v'(x)$
  -- Let $u(x) = e^{3x}$ and $v(x) = \ln(1+x^2)$
  -- Then $u'(x) = 3 e^{3x}$ and $v'(x) = \frac{2x}{1 + x^2}$
  -- Therefore $f'(x) = 3 e^{3x} \ln(1+x^2) + e^{3x} \cdot \frac{2x}{1 + x^2}$
  simp [deriv_mul, differentiableAt_exp, differentiableAt_log, deriv_const, mul_comm, deriv_id'', add_zero, zero_add, mul_one, exp_zero, log_one]
  all_goals norm_num