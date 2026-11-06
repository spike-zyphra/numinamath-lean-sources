import Mathlib

theorem algebra_322729 {x y z : ℝ} (h1 : 1988 * (x - y) + 1989 * (y - z) + 1990 * (z - x) = 0)
    (h2 : 1988^2 * (x - y) + 1989^2 * (y - z) + 1990^2 * (z - x) = 1989) :
    y - z = -1989 := by
  ring_nf at h1 h2 ⊢
  linarith