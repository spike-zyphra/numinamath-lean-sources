import Mathlib

theorem algebra_210311 {xiao_ming xiao_father : ℝ} (h : xiao_ming + xiao_father = 162) (h1 : xiao_ming = xiao_father / 2) :
    xiao_ming = 54 := by
  have eq1 : xiao_father = 108 := by
    linarith [h, h1]
  rw [eq1] at h1
  linarith