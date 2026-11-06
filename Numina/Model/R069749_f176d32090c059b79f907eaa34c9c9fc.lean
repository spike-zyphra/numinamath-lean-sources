import Mathlib

theorem algebra_139356 {x : ℝ} (hx : x ≠ 0) (h : 2000000 = x * (1 - 75 / 100)) :
    x * 0.75 = 6000000 := by 
  have hx_eq : x = 8000000 := by
    linarith
  rw [hx_eq]
  norm_num