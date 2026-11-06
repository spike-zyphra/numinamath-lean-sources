import Mathlib

theorem algebra_145970 (x y : ℝ) (h1 : 3*x+5*y=8.40) (h2 : 5*x+4*y=8.80) :
    2*x+3*y=5.20 := by
  norm_num at h1 h2 ⊢
  linarith