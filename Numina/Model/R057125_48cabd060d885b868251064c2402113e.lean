import Mathlib

theorem algebra_162973 (d : ℝ) (h : d = 1000 + 200) (v : ℝ) (h' : v > 0)
    (h'' : d / v = 10) (h''' : d / (v - 40) = t) :
    t = 15 := by
  have hd : d = 1200 := by 
    rw [h]
    norm_num
  have h1 : v = 120 := by
    rw [hd] at h''
    field_simp at h''
    nlinarith
  have h2 : v - 40 = 80 := by
    rw [h1]
    norm_num
  rw [hd, h2] at h'''
  field_simp at h'''
  linarith