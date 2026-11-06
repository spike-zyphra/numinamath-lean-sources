import Mathlib

theorem algebra_21769 (deposit : ℝ) (rate : ℝ) (time : ℝ) (hd : deposit = 10000) (hr : rate = 0.045) (ht : time = 2) :
    deposit * (1 + rate) ^ time - deposit = 920.25 := by
  rw [hd, hr, ht]
  norm_num