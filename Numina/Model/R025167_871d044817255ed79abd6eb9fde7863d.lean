import Mathlib

theorem algebra_604250 (k : ℚ) (hk : k ^ 3 = 2) (x y z : ℚ)
    (h : x + y * k + z * k ^ 2 ≠ 0) :
    ∃ u v w : ℚ, (x + y * k + z * k ^ 2) * (u + v * k + w * k ^ 2) = 1 := by
  use (x + y * k + z * k ^ 2)⁻¹, 0, 0
  simp [h]