import Mathlib

theorem algebra_98363 {x y z : ℝ} (h₀ : y = 2 * x) (h₁ : z = 2 * y) : x + y + z = 7 * x := by
  have h₂ : z = 4 * x := by
    rw [h₁, h₀]
    ring
  calc
    x + y + z = x + (2 * x) + (4 * x) := by
      rw [h₀, h₂]
    _ = (1 * x) + (2 * x) + (4 * x) := by ring
    _ = (1 + 2 + 4) * x := by ring
    _ = 7 * x := by norm_num