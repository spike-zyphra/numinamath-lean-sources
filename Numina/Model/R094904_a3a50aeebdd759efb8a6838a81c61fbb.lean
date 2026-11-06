import Mathlib

theorem algebra_174621 (p v : ℝ) (hp : p > 0) (hv : v > 0)
    (h1 : p * 60 = v * 51) (h2 : p * 78 = v * 72 + 9) :
    p * 78 - v * 72 = 1.35 := by
  nlinarith