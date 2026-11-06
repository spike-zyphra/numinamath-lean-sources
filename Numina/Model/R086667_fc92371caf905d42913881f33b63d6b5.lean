import Mathlib

theorem algebra_131181 {x : ℝ} (hx : x * 1.22 = 61.00) :
    x * 1.24 = 62.00 := by
  have hx_val : x = 61.00 / 1.22 := by 
    field_simp
    linarith
  rw [hx_val]
  norm_num