import Mathlib

theorem algebra_169090 (l v : ℝ) (hl : l > 0) (hv : v > 0)
    (h1 : l + 225 = 27 * v) (h2 : l + 225 + 9 = 9 * v) :
    l = 126 ∧ v = 60 := by 
  nlinarith