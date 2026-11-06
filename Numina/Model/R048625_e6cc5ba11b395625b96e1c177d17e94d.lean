import Mathlib

open Polynomial

theorem algebra_115 {x : ℝ} (hx : x = (1 + √1994) / 2) : (4 * x^3 - 1997 * x - 1994)^2001 = -1 := by
  have h1 : 4 * x^2 - 4 * x - 1993 = 0 := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 1994, Real.sq_sqrt (show (0 : ℝ) ≤ (1994 : ℝ) by norm_num)]
  have h2 : x^2 = x + 1993 / 4 := by
    nlinarith [h1]
  have h3 : 4 * x^3 = 1997 * x + 1993 := by
    have eq1 : x^3 = x * x^2 := by ring
    rw [eq1]
    rw [h2]
    nlinarith
  have h4 : 4 * x^3 - 1997 * x - 1994 = -1 := by
    nlinarith [h3]
  rw [h4]
  norm_num