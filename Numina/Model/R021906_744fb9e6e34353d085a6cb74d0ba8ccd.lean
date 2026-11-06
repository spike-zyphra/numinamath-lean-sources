import Mathlib

open Real

theorem algebra_235147 {x : ℝ} (hx : x = sqrt (86 + 41 * sqrt (86 + 41 * x))) :
    x = 43 := by
  have h1 : x ≥ 0 := by
    have h2 : x = sqrt (86 + 41 * sqrt (86 + 41 * x)) := hx
    have h3 : sqrt (86 + 41 * sqrt (86 + 41 * x)) ≥ 0 := Real.sqrt_nonneg (86 + 41 * sqrt (86 + 41 * x))
    linarith
  have h2 : x ^ 2 = 86 + 41 * sqrt (86 + 41 * x) := by
    calc
      x ^ 2 = (sqrt (86 + 41 * sqrt (86 + 41 * x))) ^ 2 := by rw [show sqrt (86 + 41 * sqrt (86 + 41 * x)) = x by linarith [hx]]
      _ = 86 + 41 * sqrt (86 + 41 * x) := by rw [Real.sq_sqrt]; positivity
  have h4 : (sqrt (86 + 41 * x)) ^ 2 = 86 + 41 * x := by
    rw [Real.sq_sqrt]
    nlinarith [show x ≥ 0 by linarith]
  have h5 : (x - 43) * (x + 2) = 0 := by
    nlinarith [sq_nonneg (x - 43), sq_nonneg (sqrt (86 + 41 * x) - 43), sq_nonneg (x - sqrt (86 + 41 * x)), sq_nonneg (x - 43), sq_nonneg (sqrt (86 + 41 * x) + 2), Real.sqrt_nonneg (86 + 41 * x)]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- h6 = x - 43 = 0
    linarith
  · -- h7 = x + 2 = 0
    nlinarith