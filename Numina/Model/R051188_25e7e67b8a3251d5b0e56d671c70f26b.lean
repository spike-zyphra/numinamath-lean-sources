import Mathlib

theorem algebra_266702 (l w h : ℝ) (hvol : l * w * h = 12) :
    (2 * l) * (2 * w) * (3 * h) = 144 := by
  have h1 : (2 * l) * (2 * w) * (3 * h) = 12 * (l * w * h) := by
    ring
  rw [h1, hvol]
  norm_num