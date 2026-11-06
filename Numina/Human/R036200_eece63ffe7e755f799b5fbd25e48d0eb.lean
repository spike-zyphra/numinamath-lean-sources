import Mathlib

theorem algebra_169122 {x y : ℝ} (hx : x = 2 * y) (hy : 0 < y) (hxy : x > 0) :
    (x * 0.9 + y * 0.81) / (x + y) = 0.87 := by 
  have h3 : x + y ≠ 0 := by
    linarith [hx, hy]
  rw [hx]
  field_simp [h3]
  ring_nf