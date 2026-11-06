import Mathlib

theorem algebra_563 (t : ℝ) (h1 : 60 * t = 3 * (60 * (t - 7.32))) (h2 : 60 * (t + 7.39) = 2 * (60 * (t + 7.32))) :
    t = 7.11 := by
  ring_nf at h1 h2 ⊢
  linarith