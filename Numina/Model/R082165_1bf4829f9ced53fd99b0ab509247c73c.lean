import Mathlib

theorem algebra_203033 (x y z : ℝ) (h₀ : x > 0) (h₁ : y > 0) (h₂ : z > 0)
    (h₃ : x = 1200) (h₄ : y = 2100) (h₅ : z = 1500) :
    x + y + z = 4800 := by
  rw [h₃, h₄, h₅]
  norm_num