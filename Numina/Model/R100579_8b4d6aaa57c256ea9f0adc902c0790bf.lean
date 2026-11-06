import Mathlib

theorem algebra_234489 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : 2 * x = 3 * y) :
    (2 * x + 3 * y) / (x + y) = 2.4 := by
  have hy_eq : y = (2 / 3) * x := by
    linarith

  have h1 : 2 * x + 3 * y = 4 * x := by
    rw [hy_eq]
    linarith

  have h2 : x + y = (5 / 3) * x := by
    rw [hy_eq]
    linarith
  
  have pos1 : x + y ≠ 0 := by
    have hx_pos : x > 0 := hx
    have hy_pos : y > 0 := hy
    have hxy_pos : x + y > 0 := by linarith
    linarith
  
  rw [h1, h2]
  field_simp [pos1]
  <;> ring_nf <;> linarith