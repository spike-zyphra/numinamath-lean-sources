import Mathlib

theorem algebra_94706 (x y z : ℕ) (h₀ : x * 2 = y * 3) (h₁ : z = x + 1) (h₂ : x * 2 + y * 3 + z = 61) :
    z = 13 := by
  rw [h₁] at h₂
  have h3 : x * 2 + y * 3 + (x + 1) = 61 := by
    omega
  have eq1 : x + y = 20 := by
    omega
  have hx : x = 12 := by
    omega
  have hy : y = 8 := by
    omega
  have hz : z = 13 := by
    omega
  exact hz