import Mathlib

theorem algebra_220154 (j x t : ℕ) (hj : j > 0) (hx : x > 0) (ht : t > 0)
    (h1 : x - 12 = 4 * (j + 12)) (h2 : t - 20 = x + 15) (h3 : x + 17 = t - 17) :
    j + x + t = 193 := by
  omega