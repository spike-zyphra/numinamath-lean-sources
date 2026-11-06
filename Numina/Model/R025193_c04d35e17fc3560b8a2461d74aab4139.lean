import Mathlib

theorem algebra_198546 (x y z : ℝ) (h₀ : x * (y + z) = 5) (h₁ : y * (x + z) = 8)
    (h₂ : z * (x + y) = 9) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = -1 ∧ y = -2 ∧ z = -3) := by
  have h3 : (x - 1) * (x + 1) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  cases' (mul_eq_zero.mp h3) with hx1 hx2
  · -- Case x - 1 = 0, so x = 1
    have hx : x = 1 := by linarith
    have hy : y = 2 := by
      nlinarith [hx]
    have hz : z = 3 := by
      nlinarith [hx, hy]
    left
    exact ⟨hx, hy, hz⟩
  · -- Case x + 1 = 0, so x = -1
    have hx : x = -1 := by linarith
    have hy : y = -2 := by
      nlinarith [hx]
    have hz : z = -3 := by
      nlinarith [hx, hy]
    right
    exact ⟨hx, hy, hz⟩