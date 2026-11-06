import Mathlib

theorem algebra_110098 {a b : ℝ} (ha : a ^ 5 + b ^ 5 = 3) (hb : a ^ 15 + b ^ 15 = 9) :
    a ^ 10 + b ^ 10 = 5 := by 
  have h1 : a ^ 15 + b ^ 15 = (a ^ 5 + b ^ 5) * (a ^ 10 - a ^ 5 * b ^ 5 + b ^ 10) := by
    ring_nf
  rw [h1] at hb
  rw [ha] at hb
  nlinarith [sq_nonneg (a ^ 5 - b ^ 5)]