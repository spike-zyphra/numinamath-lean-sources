import Mathlib

theorem algebra_83968 (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (h1 : y = x - 2003) (h2 : z = 2 * y - 2003) (h3 : w = 3 * z - 2003) :
    x ≥ 10015 / 3 := by
  linarith