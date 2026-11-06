import Mathlib

theorem algebra_14591 {x y : ℝ} (hx : x + y = 24) (hy : 99*x+45*y=1809) :
    x=13.5 := by
  have h2 : y = 24 - x := by
    linarith
  rw [h2] at hy
  norm_num at hy ⊢
  linarith