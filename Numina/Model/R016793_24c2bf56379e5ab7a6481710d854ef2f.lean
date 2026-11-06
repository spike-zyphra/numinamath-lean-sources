import Mathlib

theorem algebra_561 (xiao_ming xiao_father : ℝ)
    (h1 : xiao_ming = 8.08) (h2 : xiao_father = 8.08 + 8 / 60) (h3 : 4 / xiao_ming = 8 / xiao_father) :
    xiao_father = 8.32 := by 
  rw [h1] at h3
  rw [h2] at h3
  norm_num at h3 ⊢
  <;> linarith