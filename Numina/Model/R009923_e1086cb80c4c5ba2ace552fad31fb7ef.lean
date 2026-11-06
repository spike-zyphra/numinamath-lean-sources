import Mathlib

theorem algebra_20457 {x y z : ℝ} (h₀ : x + y + z = 0) (h₁ : x * y * z = 17) :
    x^3 + y^3 + z^3 = 51 := by
  have h2 : x ^ 3 + y ^ 3 + z ^ 3 = 3 * (x * y * z) := by
    have h2' : x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z) =
        (x + y + z) * (x^2 + y^2 + z^2 - (x * y + y * z + z * x)) := by
      ring
    rw [show x + y + z = 0 by linarith] at h2'
    linarith
  rw [h2]
  rw [h₁]
  norm_num