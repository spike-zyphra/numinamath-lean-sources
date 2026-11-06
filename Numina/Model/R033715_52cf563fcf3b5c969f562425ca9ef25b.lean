import Mathlib

theorem algebra_236238 (x : ℝ) (hx : x^3 - x - 1 = 0) (hxp : ∀ x' : ℝ, x'^3 - x' - 1 = 0 → x' = x) :
    ∃ z : ℝ, z = x^2 + 3 * x + 1 ∧ z^3 - 5 * z^2 - 10 * z - 11 = 0 := by
  use x^2 + 3 * x + 1
  constructor
  . 
    rfl
  . 
    have eq1 : x^3 = x + 1 := by 
      linarith 
    nlinarith [sq_nonneg (x^2 + x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2 -1), sq_nonneg (x^2 - x -1), sq_nonneg (x^2 + 3 * x +1), sq_nonneg (x), sq_nonneg (x^2), sq_nonneg (x^3 - x -1)]