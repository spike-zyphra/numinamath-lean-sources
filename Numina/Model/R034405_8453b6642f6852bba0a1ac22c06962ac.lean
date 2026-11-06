import Mathlib

theorem algebra_218790 (x y z : ℝ) :
    (x^2 + 1) * y = z^2 + 1 ∧ (y^2 + 1) * z = x^2 + 1 ∧ (z^2 + 1) * x = y^2 + 1 ↔
    (x, y, z) = (1, 1, 1) := by
  constructor
  · -- Assume we have the conjunction of equations, need to prove (1,1,1).
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : x - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x * y * z - 1), sq_nonneg (x * z - 1), sq_nonneg (y * x - 1), sq_nonneg (y * z - 1)]
    have hx1 : x = 1 := by linarith
    have h5 : y - 1 = 0 := by
      rw [show x = 1 by linarith] at h₁ h₂ h₃
      nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hy1 : y = 1 := by linarith
    have h6 : z - 1 = 0 := by
      rw [show x = 1 by linarith, show y = 1 by linarith] at h₁ h₂ h₃
      nlinarith [sq_nonneg (z - 1)]
    have hz1 : z = 1 := by linarith
    simp [hx1, hy1, hz1]
  · -- Assume (x, y, z) = (1, 1, 1), need to prove the equations.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num