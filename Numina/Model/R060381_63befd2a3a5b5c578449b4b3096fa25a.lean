import Mathlib

theorem algebra_323660 (x y z : ℝ) :
    (x + y = 2 ∧ x * y - z ^ 2 = 1) ↔ (x, y, z) = (1, 1, 0) := by
  constructor
  · -- Assume the system of equations, prove (x, y, z) = (1, 1, 0)
    rintro ⟨h1, h2⟩
    have h3 : y = 2 - x := by linarith
    rw [h3] at h2
    have h4 : (x - 1) ^ 2 + z ^ 2 = 0 := by
      nlinarith
    have h5 : (x - 1) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 1), sq_nonneg z]
    have h6 : x - 1 = 0 := by
      rwa [sq_eq_zero_iff] at h5
    have hx1 : x = 1 := by linarith
    have h7 : z ^ 2 = 0 := by
      linarith [sq_nonneg (x - 1), sq_nonneg z]
    have hz1 : z = 0 := by
      rwa [sq_eq_zero_iff] at h7
    have hy1 : y = 1 := by
      rw [hx1] at h3
      linarith
    simp [Prod.ext_iff, hx1, hy1, hz1]
  · -- Assume (x, y, z) = (1, 1, 0), prove the system of equations
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check first equation
      norm_num
    · -- Check second equation
      norm_num