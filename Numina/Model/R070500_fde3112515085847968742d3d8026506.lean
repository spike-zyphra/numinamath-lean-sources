import Mathlib

theorem algebra_319632 {a b c : ℝ} (ha : a ≠ 0) (t : ℝ)
    (h : a * t^2 + b * t + c = 0) :
    b^2 - 4 * a * c = (2 * a * t + b)^2 := by
  have hc : c = -a * t^2 - b * t := by 
    linarith
  rw [hc]
  ring