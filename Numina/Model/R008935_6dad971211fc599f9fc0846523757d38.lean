import Mathlib

  theorem algebra_193423 {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x = 1.4 * y) (h : x * 6 + y * 8 = 820) :
    x * 6 = 420 ∧ y * 8 = 400 := by
  have hy_val : y = 50 := by
    rw [hxy] at h
    norm_num at h ⊢
    linarith
  have hx_val : x = 70 := by
    rw [hy_val] at hxy
    norm_num at hxy ⊢
    linarith
  constructor
  · -- Show x * 6 = 420
    rw [hx_val]
    norm_num
  · -- Show y * 8 = 400
    rw [hy_val]
    norm_num