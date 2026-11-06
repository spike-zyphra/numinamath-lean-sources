import Mathlib

theorem algebra_11828 {l w : ℕ} (hw : l = 3 * w) (hperim : 2 * (l + w) = 160) :
    l * w = 1200 := by 
  rw [hw] at hperim
  have hw2 : w = 20 := by
    omega
  have hl2 : l = 60 := by
    nlinarith [hw, hw2]
  calc
    l * w = 60 * 20 := by rw [hl2, hw2]
    _ = 1200 := by norm_num