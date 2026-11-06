import Mathlib

theorem number_theory_286689 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : 27 * x + 28 * y + 29 * z = 363) : 10 * (x + y + z) = 130 := by
  omega