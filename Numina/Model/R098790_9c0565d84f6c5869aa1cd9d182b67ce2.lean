import Mathlib

open Real

theorem calculus_138033 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 / 10 + 3) (x0 : ℝ) (hx0 : x0 = 2) :
    deriv f x0 * (x - x0) + f x0 = 2 / 5 * x + 13 / 5 := by
  rw [hx0]
  have h1 : f = fun x => x ^ 2 / 10 + 3 := by exact hf
  have h2 : deriv f 2 = 2 / 5 := by
    rw [h1]
    simp [deriv_add, deriv_pow, deriv_const, deriv_id', mul_comm]
    all_goals norm_num
  have h3 : f 2 = 17 / 5 := by 
    rw [h1]
    norm_num
  rw [h2, h3]
  ring