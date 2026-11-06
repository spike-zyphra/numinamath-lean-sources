import Mathlib

theorem algebra_308987 {x y : ℝ} (h₀ : y + 4 = (x - 2)^2) (h₁ : x + 4 = (y - 2)^2) (h₂ : x ≠ y) :
    x^2 + y^2 = 15 := by
  have h3 : y - x = (x - y) * (x + y - 4) := by
    nlinarith [h₀, h₁]
  have h4 : x + y = 3 := by
    have h5 : x - y ≠ 0 := sub_ne_zero.mpr h₂
    have h6 : -(x - y) = (x - y) * (x + y - 4) := by linarith
    have h7 : -1 = x + y - 4 := by
      apply (mul_left_inj' h5).mp
      linarith
    linarith
  nlinarith [h₀, h₁, h4]