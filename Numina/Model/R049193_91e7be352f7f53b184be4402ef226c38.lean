import Mathlib

theorem algebra_95783 (j m : ℝ) (hj : j > 0) (hm : m > 0)
(hj1 : j * (3 / 5) = m * (4 / 5)) (hj2 : j * 5 = m * 2) :
m = 5 := by
  nlinarith