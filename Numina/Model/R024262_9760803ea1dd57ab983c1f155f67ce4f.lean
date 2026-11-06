import Mathlib

theorem algebra_5395 {a b : ℝ} (h : a^2-4*a+b^2-8*b+20=0) :
    ∃ x, a*x-6=2^b ↔ x=11 := by
  have h1 : (a - 2) ^ 2 + (b - 4) ^ 2 = 0 := by
    nlinarith [h]
  have ha1 : a - 2 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 4), h1]
  have hb1 : b - 4 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 4), h1]
  have ha2 : a = 2 := by linarith [ha1]
  have hb2 : b = 4 := by linarith [hb1]
  use 11
  rw [ha2, hb2]
  norm_num
  <;> norm_num
  <;> tauto