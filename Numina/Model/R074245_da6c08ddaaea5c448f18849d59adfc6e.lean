import Mathlib

theorem algebra_271736 {x : ℝ} (hx : x ≠ 0) (h : 0.6 * x = 42) :
    0.5 * x = 35 := by 
  have hx_eq : x = (42 / (0.6 : ℝ)) := by 
    field_simp
    linarith
  rw [hx_eq]
  norm_num