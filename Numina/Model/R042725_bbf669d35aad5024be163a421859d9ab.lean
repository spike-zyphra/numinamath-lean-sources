import Mathlib

open Real

theorem calculus_140558 (f : ℝ → ℝ) (hf : f = fun x => 3 * (x ^ ((1 : ℝ) / 3) - 2 * sqrt x)) (x0 : ℝ) (hx0 : x0 = 1) :
    deriv f x0 = -2 ∧ f x0 = -2 * x0 - 1 := by
  rw [hx0]
  constructor
  · -- First part: proving that the derivative is -2
    rw [hf]
    simp [deriv_sub, deriv_const_mul, deriv_pow, deriv_sqrt, mul_comm]
    all_goals norm_num [sqrt_eq_rpow]
    all_goals norm_num
  · -- Second part: proving that f 1 = -2 * 1 - 1
    rw [hf]
    norm_num [sqrt_eq_rpow]
    all_goals norm_num