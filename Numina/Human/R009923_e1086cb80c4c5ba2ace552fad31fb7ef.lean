import Mathlib

/- If the sum of three real numbers is $0$ and their product is $17$, then what is the sum of their cubes? -/
theorem algebra_20457 {x y z : ℝ} (h₀ : x + y + z = 0) (h₁ : x * y * z = 17) :
    x^3 + y^3 + z^3 = 51 := by
  have h₂ : x = -y - z := by linarith
  rw [h₂] at h₁ ⊢
  nlinarith