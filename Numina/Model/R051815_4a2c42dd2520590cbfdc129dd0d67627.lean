import Mathlib

open Real

theorem calculus_135883 (f : ℝ → ℝ) (hf : f = fun x => (x^2 - 3 * x + 3) / 3) (x0 : ℝ) (hx0 : x0 = 3) :
    deriv f x0 = 1 ∧ f x0 = x0 - 2 := by 
  rw [hx0]
  constructor
  · -- First part: deriving $f'(3) = 1$
    rw [hf]
    simp [deriv_div, deriv_pow, deriv_sub, deriv_add, deriv_id', mul_comm, mul_assoc, mul_left_comm]
    all_goals norm_num [deriv_const, deriv_id', mul_comm]
  · -- Second part: proving $f(3) = 3 - 2$
    rw [hf]
    norm_num