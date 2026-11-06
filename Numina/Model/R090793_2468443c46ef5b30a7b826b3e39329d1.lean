import Mathlib

open Real

theorem algebra_9581 {x : ℝ} (hx : x = Real.sqrt (72 + 6 * x)) (hx1 : 0 ≤ x) : x = 12 := by
  have h1 : x ^ 2 = 72 + 6 * x := by 
    rw [hx]
    have h2 : (Real.sqrt (72 + 6 * x)) ^ 2 = 72 + 6 * x := by
      apply Real.sq_sqrt 
      linarith
    linarith [h2]
  have h3 : x ^ 2 - 6 * x - 72 = 0 := by 
    linarith
  have h4 : (x - 12) * (x + 6) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h4) with h5 h6 
  · 
    linarith 
  · 
    have h7 : x = -6 := by 
      linarith 
    linarith [show x ≥ 0 by linarith, h7]