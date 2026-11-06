import Mathlib

theorem algebra_115947 (xiao_ming xiao_ming_brother xiao_father xiao_mother : ℕ)
    (h : xiao_father = 30) (h' : xiao_mother = xiao_father - 2)
    (h'' : xiao_ming_brother = 3 * xiao_ming) (h''' : xiao_father + xiao_mother + xiao_ming_brother + xiao_ming = 114) :
    xiao_ming = 14 := by 
  have h1 : xiao_father = 30 := h
  have h2 : xiao_mother = 28 := by 
    rw [h'] 
    rw [h1]
    all_goals omega 
  rw [h1, h2, h''] at h'''
  omega