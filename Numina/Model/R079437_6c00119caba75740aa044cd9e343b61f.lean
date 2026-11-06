import Mathlib

theorem inequalities_71586 :
    (1 / 2 : ℝ)^3 + (2 / 3)^3 + (5 / 6)^3 = 1 ∧ 3^33 + 4^33 + 5^33 < 6^33 := by 
  constructor
  · norm_num
  · norm_num