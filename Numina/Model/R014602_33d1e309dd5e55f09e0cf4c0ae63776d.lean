import Mathlib

theorem algebra_195272 {x y : ℝ} (hx : x ≠ -2 * y) (hy : 10 * x - 3 * y = 2 * (x + 2 * y)) :
    (y + x) / (y - x) = 15 := by
  have h1 : 8 * x = 7 * y := by
    linarith
  have h2 : y - x ≠ 0 := by
    by_contra h
    have h3 : y = x := by linarith
    have h4 : x = 0 := by
      rw [show y = x by linarith [h3]] at h1
      linarith
    have h5 : y = 0 := by
      linarith [h4, h3]
    have h6 : x = -2 * y := by
      linarith [h4, h5]
    contradiction
  have h3 : y = 8 / 7 * x := by
    linarith
  have h4 : y + x = 15 / 7 * x := by
    rw [h3]
    linarith
  have h5 : y - x = 1 / 7 * x := by
    rw [h3]
    linarith
  have hx1 : x ≠ 0 := by
    by_contra h
    have h6 : x = 0 := by linarith
    have h7 : y = 0 := by
      rw [h6] at h1
      linarith
    have h8 : x = -2 * y := by
      linarith [h6, h7]
    contradiction
  rw [h4, h5]
  have h7 : x ≠ 0 := hx1
  field_simp [h7]
  <;> 
  ring_nf
  <;> 
  field_simp [h7]