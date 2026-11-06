import Mathlib

theorem algebra_12743 {x : ℝ} (hx : x = (19.90 + 6.95) / 200 * 100) :
    round x = 13 := by 
  rw [hx]
  norm_num [round_eq]
  <;> norm_num