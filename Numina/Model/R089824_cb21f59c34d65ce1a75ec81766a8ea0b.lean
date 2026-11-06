import Mathlib

theorem algebra_193532 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x + y + z = 1) (h2 : y = 1.08 * x) (h3 : z = 11 * x + 25 * y + 12 * z)
    (h4 : z = 13.5 * x + 11 * y + 25 * z) :
    (y - x) / x * 100 = 13.2 := by
  have h5 : z < 0 := by
    have eq2 : y = 1.08 * x := h2
    nlinarith
  linarith