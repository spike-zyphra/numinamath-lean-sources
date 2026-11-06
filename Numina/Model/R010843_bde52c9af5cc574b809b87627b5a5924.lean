import Mathlib

theorem algebra_16312 {w x y z : ℝ} (h₀ : w + x + y = -2) (h₁ : w + x + z = 4)
    (h₂ : w + y + z = 19) (h₃ : x + y + z = 12) : w * x + y * z = 99 := by
  have h4 : w + x + y + z = 11 := by
    linarith
  have hz : z = 13 := by
    linarith
  have hy : y = 7 := by
    linarith
  have hx : x = -8 := by
    linarith
  have hw : w = -1 := by
    linarith
  rw [hw, hx, hy, hz]
  norm_num