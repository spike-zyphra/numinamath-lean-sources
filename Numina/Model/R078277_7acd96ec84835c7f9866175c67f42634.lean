import Mathlib

theorem algebra_185505 (v : ℝ) (h : v > 0) (h' : 9 * v = 8 * (1.6 * v) + 40) :
    (1.6 * v) / v = 1.3 := by
  have h1 : 9 * v = 8 * (1.6 * v) + 40 := h'
  ring_nf at h1 
  nlinarith