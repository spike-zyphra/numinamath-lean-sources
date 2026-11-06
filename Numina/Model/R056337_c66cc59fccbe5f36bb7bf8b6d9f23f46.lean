import Mathlib

theorem algebra_21627 {l w : ℕ} (hw : l = 4 * w) (hperim : 2 * (l + w) = 100) :
    l * w = 400 := by 
  rw [hw] at hperim 
  have hw_eq : w = 10 := by
    omega 
  have hl_eq : 4 * w = 40 := by 
    omega 
  calc 
    l * w = (4 * w) * w := by rw [hw]
    _ = 40 * 10 := by rw [show 4 * w = 40 by omega, show w = 10 by omega]
    _ = 400 := by norm_num