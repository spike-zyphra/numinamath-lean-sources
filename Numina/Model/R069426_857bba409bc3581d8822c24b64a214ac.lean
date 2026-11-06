import Mathlib

theorem algebra_221180 {a b : ℝ} (x y : ℝ) (h₁ : x - y = a) (h₂ : x * y = b) :
    y^2 + a * y - b = 0 := by
  have hx : x = y + a := by linarith
  rw [hx] at h₂
  -- Now we have (y + a) * y = b
  -- Expanding (y + a) * y = y^2 + a * y
  -- So we have y^2 + a * y = b
  -- Rearranging we get y^2 + a * y - b = 0
  have eq1 : (y + a) * y = b := h₂
  -- Expanding left-hand side
  ring_nf at eq1 ⊢
  linarith