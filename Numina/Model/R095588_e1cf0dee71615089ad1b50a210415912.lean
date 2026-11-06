import Mathlib

theorem calculus_139654 (f : ℝ → ℝ) (hf : f = fun x => (x^2 - 2 * x - 3) / 4) (x0 : ℝ) (hx0 : x0 = 4) :
    deriv f x0 * (x - x0) + f x0 = (3 / 2) * x - 19 / 4 := by
  rw [hx0]
  have h1 : f = fun x => (x^2 - 2 * x - 3) / 4 := by
    exact hf
  have h2 : deriv f 4 = 3 / 2 := by
    rw [h1]
    simp [deriv_div, deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num [deriv_id', mul_comm]
  have h3 : f 4 = 5 / 4 := by
    rw [h1]
    norm_num
  rw [h2, h3]
  ring