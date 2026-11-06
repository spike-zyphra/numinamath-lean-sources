import Mathlib

theorem algebra_101550 (a : ℝ) (ha : 0 < a)
    (h1 : 6 * 35 * a = 1/3) :
    35 + (1 - 1/3) / (12 * a) = 70 := by 
  have ha_eq : a = 1 / 630 := by 
    linarith 
  have h2 : 12 * a = 2 / 105 := by 
    rw [ha_eq]
    norm_num 
  have h3 : (1 - 1/3 : ℝ) / (12 * a) = 35 := by 
    rw [show 12 * a = 2 / 105 by linarith [h2]]
    norm_num 
  rw [h3]
  all_goals norm_num