import Mathlib

theorem algebra_275255 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + 12 = y - 12) (h2 : x + 12 + (y - 12) / 2 = 4 * (y - 12 - (y - 12) / 2)) :
    y - 12 - (y - 12) / 2 = 24 := by
  omega