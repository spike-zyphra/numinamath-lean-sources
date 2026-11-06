import Mathlib

theorem algebra_21611 {x : ℝ} (hx : x > 2) (h : 2 * (x + 2 + x - 2) = 56) :
    (x + 2) * (x - 2) = 192 := by
  have hx_eq : x = 14 := by
    linarith 
  rw [hx_eq]
  norm_num