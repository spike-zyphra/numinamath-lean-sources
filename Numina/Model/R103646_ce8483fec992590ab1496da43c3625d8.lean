import Mathlib

theorem algebra_241821 (x : ℝ) (hx : x ≠ 0) (h1 : 20 / 100 * x + 16 = 30 / 100 * (x - 20 / 100 * x - 16) + 20)
    (h2 : 30 / 100 * (x - 20 / 100 * x - 16) + 20 = 75 / 100 * (x - 20 / 100 * x - 16 - 20) + 30) :
    x = 945 := by
  nlinarith