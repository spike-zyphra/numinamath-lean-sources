import Mathlib

theorem algebra_229718 (l : ℝ) (hl : l = 720) (v1 v2 : ℝ)
    (h1 : v1 = l / (4 * 60)) (h2 : v2 = l / (5 * 60)) :
    v2 * (l / (v1 + v2)) = 320 := by
  rw [hl] at h1 h2 ⊢
  have hv1 : v1 = 3 := by 
    rw [h1]
    norm_num
  have hv2 : v2 = 12 / 5 := by 
    rw [h2]
    norm_num
  rw [hv1, hv2]
  norm_num