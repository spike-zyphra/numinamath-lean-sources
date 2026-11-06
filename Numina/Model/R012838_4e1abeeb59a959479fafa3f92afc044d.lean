import Mathlib

theorem algebra_178270 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a = 1 / 60) (h2 : b = 1 / (60 * 75 / 100)) :
    (1 - (a * 20 + b * 20)) / b = 10 := by 
  have hb' : b = 1 / 45 := by
    rw [h2]
    norm_num
  have h3 : a * 20 + b * 20 = 7 / 9 := by
    rw [h1, hb']
    norm_num
  rw [h3, hb']
  norm_num