import Mathlib

theorem algebra_611198 (x : ℝ) (hx : x ^ 3 + 4 * x = 8) : x ^ 7 + 64 * x ^ 2 = 128 := by
  have eq1 : x ^ 3 = 8 - 4 * x := by
    linarith
  have eq2 : x ^ 7 = (x ^ 3) ^ 2 * x := by
    ring
  rw [eq2]
  rw [eq1]
  have eq3 : (8 - 4 * x) ^ 2 * x + 64 * x ^ 2 = 64 * x + 16 * x ^ 3 := by
    nlinarith
  have eq4 : 64 * x + 16 * x ^ 3 = 128 := by
    have eq5 : x ^ 3 + 4 * x = 8 := hx
    have eq6 : 16 * (x ^ 3 + 4 * x) = 16 * 8 := by
      rw [show x ^ 3 + 4 * x = 8 by linarith]
    linarith
  linarith [eq3, eq4]