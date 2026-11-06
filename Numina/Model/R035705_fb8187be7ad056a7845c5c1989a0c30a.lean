import Mathlib

theorem algebra_96787 (s e one tot: ℝ) (hs : s = 1) (he : e = 2+40/60) 
(hone : one = (e-s) / 2 ) (htot: tot = 3 * one):
s + tot = 3+30/60 := by
  rw [htot]
  rw [hs]
  rw [hone]
  rw [show s = (1: ℝ) by linarith [hs], show e = (2 + 40 / 60: ℝ) by linarith [he]]
  norm_num
  <;> linarith