import Mathlib

theorem algebra_4035 {w x y z : ℝ} (h₀ : w + x + y = -2) (h₁ : w + x + z = 4) (h₂ : w + y + z = 19) (h₃ : x + y + z = 12) : w * x + y * z = 99 := by
  have h4 : w + x + y + z = 11 := by
    linarith
  have h5 : z = 13 := by
    linarith [h₀, h4]
  have h6 : y = 7 := by
    linarith [h₁, h4]
  have h7 : x = -8 := by
    linarith [h₂, h4]
  have h8 : w = -1 := by
    linarith [h₃, h4]
  rw [show w = -1 by linarith [h8], show x = -8 by linarith [h7], show y = 7 by linarith [h6], show z = 13 by linarith [h5]]
  norm_num