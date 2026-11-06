import Mathlib

open Real

theorem inequalities_2122 (x y : ℝ) (hy : 0 < y) (hxy : x + y < 0) : ¬(x^3 * y > 0) := by
  intro h
  have h1 : x < 0 := by linarith
  have h2 : x^3 > 0 := by nlinarith [hy]
  have h3 : x > 0 := by
    nlinarith [sq_nonneg (x), sq_nonneg (x^3 - 0), sq_nonneg (x - 0)]
  linarith