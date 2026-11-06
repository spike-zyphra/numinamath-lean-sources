import Mathlib

theorem algebra_180606 (d t : ℝ) (ht : t > 0) (h : d / 4 = 14 * t) (h' : d / 2 = 15 * t)
    (h'' : d / 3 = 15.3 * t) :
    d / 4 = 15.48 * t := by
  ring_nf at h h' h'' ⊢
  linarith