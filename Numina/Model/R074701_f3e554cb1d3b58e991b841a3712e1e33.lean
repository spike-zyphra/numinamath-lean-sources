import Mathlib

theorem algebra_184248 (V : ℝ) (hV : V > 5) (h : (V + 5) / (V - 5) = 600 / 225) :
    V = 11 := by
  have h1 : V - 5 ≠ 0 := by linarith
  field_simp [h1] at h
  linarith