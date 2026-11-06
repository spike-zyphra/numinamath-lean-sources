import Mathlib

open Real

theorem calculus_131689 (f : ℝ → ℝ) (hf : f = fun x => 6 * x ^ ((1 : ℝ) / 3) - 16 * x ^ ((1 : ℝ) / 4) / 3)
    (x0 : ℝ) (hx0 : x0 = 1) :
    deriv f x0 = 2 / 3 ∧ f x0 = 2 / 3 * x0 := by
  rw [hx0]
  constructor
  · -- show that the derivative of f at 1 is 2 / 3
    rw [hf]
    simp [deriv_sub, deriv_div, deriv_pow, deriv_const, mul_comm]
    norm_num [deriv_pow, deriv_id', mul_comm]
    all_goals norm_num
  · -- show that f 1 = 2 / 3 * 1
    rw [hf]
    all_goals norm_num