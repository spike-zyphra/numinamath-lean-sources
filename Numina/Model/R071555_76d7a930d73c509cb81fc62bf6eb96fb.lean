import Mathlib

theorem algebra_101851 (d : ℝ) (h : d > 0) (h1 : 40 * t1 + 60 * t2 = d) (h2 : 40 * (1.5 * t1) + 60 * (1.5 * t2) = d - 50) :
    d = 1000 / 7 := by
  ring_nf at h2
  nlinarith