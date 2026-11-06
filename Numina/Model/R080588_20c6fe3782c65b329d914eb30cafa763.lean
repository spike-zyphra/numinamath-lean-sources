import Mathlib

theorem algebra_12304 {x y : ℝ} (hx : x ≠ -1 / 3) (hy : y = 1 / (3 * x + 1)) (h : y = 1) :
    x = 0 := by 
  rw [hy] at h
  have h1 : 3 * x + 1 ≠ 0 := by
    intro h2 
    have : x = -1 / 3 := by linarith 
    contradiction 
  field_simp [h1] at h 
  linarith