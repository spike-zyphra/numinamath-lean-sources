import Mathlib

theorem algebra_19634 (x : ℝ) (h : (x + 3)^2 + 2^2 = (x + 2)^2 + 3^2) :
    Real.sqrt ((x + 3)^2 + 2^2) = Real.sqrt 13 := by 
  have hx : x = 0 := by
    linarith [h]
  rw [hx]
  norm_num
  <;> ring_nf <;> norm_num