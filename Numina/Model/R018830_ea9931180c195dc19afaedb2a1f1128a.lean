import Mathlib

theorem algebra_113933 (xiao_ming xiao_father : ℝ)
    (h1 : xiao_ming = 8.08) (h2 : xiao_father = xiao_ming + 8 / 60) (h3 : xiao_father * 4 = xiao_ming * 8) :
    xiao_father = 8.32 := by 
  rw [h1] at h2 h3
  have h4 : xiao_father = 8.08 + (8 / 60 : ℝ) := by 
    linarith 
  rw [h4] at h3 
  norm_num at h3 
  all_goals 
    linarith