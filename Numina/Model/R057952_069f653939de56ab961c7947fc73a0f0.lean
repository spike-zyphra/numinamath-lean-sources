import Mathlib

theorem algebra_269882 (d : ℝ) (h : d > 0) (v : ℝ) (h' : v > 0)
    (h1 : d / 21 = d / v + 5) :
    5 = d / 21 - d / v := by 
  have h2 : v ≠ 0 := by linarith
  field_simp [h2] at h1 ⊢
  linarith