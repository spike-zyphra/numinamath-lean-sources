import Mathlib

theorem algebra_2404 {a b c : ℝ}
    (ha : a = -123.4 - (-123.5)) (hb : b = 123.4 - 123.5) (hc : c = 123.4 - (-123.5)) :
    c > a ∧ a > b := by
  have ha1 : a = 0.1 := by 
    rw [ha]
    norm_num
  have hb1 : b = -0.1 := by 
    rw [hb]
    norm_num
  constructor
  · -- Show c > a
    rw [ha1]
    linarith [hc]
  · -- Show a > b
    rw [ha1, hb1]
    norm_num