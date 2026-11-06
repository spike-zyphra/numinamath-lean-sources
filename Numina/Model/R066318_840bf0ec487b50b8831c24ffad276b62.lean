import Mathlib

theorem algebra_247092 {x : ℝ} (hx : x ≠ 0) (hxp : x ≠ 1) (hxp' : x ≠ -1)
    (h : x^2 = (1 / (1 / x - 1 / (x + 1))) - x) :
    x^2 = (1 / (1 / x - 1 / (x + 1))) - x := by 
  exact h