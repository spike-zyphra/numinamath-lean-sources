import Mathlib

theorem algebra_199904 (l t : ℝ) (hl : l > 0) (ht : t > 0)
    (h : (1 / 2) * l^2 * t^2 = l^2 * (t / 3)^2) :
    t = 3 * Real.sqrt 3 * t := by
  have eq1 : (1 / 2) * l^2 * t^2 = l^2 * (t / 3) ^ 2 := by
    linarith [h]

  have eq2 : (1 / 2) * t^2 = (t / 3) ^ 2 := by
    have h1 : l^2 > 0 := by
      nlinarith
    apply (mul_left_inj' (show l^2 ≠ 0 by linarith)).mp
    nlinarith
  have eq3 : (1 / 2) * t ^ 2 = t ^ 2 / 9 := by
    have eq4 : (t / 3) ^ 2 = t ^ 2 / 9 := by
      ring_nf
    nlinarith [eq2, eq4]
  have eq4 : 7 * t ^ 2 = 0 := by
    nlinarith [eq3]
  have eq5 : t ^ 2 = 0 := by
    nlinarith
  have eq6 : t = 0 := by
    nlinarith
  -- This contradicts with t > 0
  linarith