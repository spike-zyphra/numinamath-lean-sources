import Mathlib

open Real

theorem calculus_137813 {f : ℝ → ℝ} (hf : f = fun x => exp x * (x^2 + 3)) :
    deriv f 0 = 3 := by
  rw [hf]
  -- Apply the product rule for differentiation
  -- f(x) = exp(x) * (x^2 + 3)
  -- f'(x) = exp(x) * (x^2 + 3) + exp(x) * 2x
  -- f'(0) = exp(0) * (0^2 + 3) + exp(0) * 2*0 = 1 * 3 + 1 * 0 = 3
  simp [deriv_mul, deriv_add, deriv_pow, deriv_id'', mul_comm]
  all_goals norm_num