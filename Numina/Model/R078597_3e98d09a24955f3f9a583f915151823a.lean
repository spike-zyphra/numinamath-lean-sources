import Mathlib

theorem algebra_19407 (x y z : ℝ) (h₀ : x + y + z = 185) (h₁ : y = z) (h₂ : x - y = 20) :
    x = 75 := by
  have h3 : z = y := by linarith [h₁]
  rw [h3] at h₀
  linarith