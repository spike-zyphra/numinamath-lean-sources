import Mathlib

theorem algebra_15218 {l w : ℕ} (hw : l = w * 2 + 25) (hperim : 2 * (l + w) = 650) :
    l * w = 22500 := by
  have h1 : l + w = 325 := by
    omega
  rw [hw] at h1
  have hw2 : w = 100 := by 
    omega
  have hl : l = 225 := by 
    rw [hw2] at hw
    omega
  calc
    l * w = 225 * 100 := by rw [hl, hw2]
    _ = 22500 := by norm_num