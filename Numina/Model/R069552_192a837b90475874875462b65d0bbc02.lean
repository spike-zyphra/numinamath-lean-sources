import Mathlib

open Real

theorem calculus_142786 (f : ℝ → ℝ) (hf : f = fun x => (x^29 + 6) / (x^4 + 1)) (x0 : ℝ) (hx0 : x0 = 1) :
    deriv f x0 = 7.5 ∧ f x0 = 7.5 * x0 - 4 := by
  rw [hx0]
  constructor
  · -- Calculate the derivative at x0 = 1
    rw [hf]
    simp [deriv_div, deriv_add, deriv_pow, deriv_const, mul_comm]
    all_goals norm_num
  · -- Calculate the function value at x0 = 1
    rw [hf]
    all_goals norm_num