import Mathlib

theorem algebra_48848 (a : ℝ) : Real.sin a ^ 3 * Real.cos (3 * a) + Real.cos a ^ 3 * Real.sin (3 * a) = 3 / 4 * Real.sin (4 * a) := by
  have h1 : Real.cos (3 * a) = 4 * Real.cos a ^ 3 - 3 * Real.cos a := by
    rw [Real.cos_three_mul]
  have h2 : Real.sin (3 * a) = 3 * Real.sin a - 4 * Real.sin a ^ 3 := by
    rw [Real.sin_three_mul]
  have h3 : Real.sin (4 * a) = 2 * Real.sin (2 * a) * Real.cos (2 * a) := by
    have h1 : Real.sin (4 * a) = Real.sin (2 * (2 * a)) := by ring_nf
    rw [h1]
    rw [show Real.sin (2 * (2 * a)) = 2 * Real.sin (2 * a) * Real.cos (2 * a) by rw [Real.sin_two_mul]]
  have h4 : Real.sin (2 * a) = 2 * Real.sin a * Real.cos a := by
    rw [Real.sin_two_mul]
  have h5 : Real.cos (2 * a) = 2 * Real.cos a ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h1, h2, h3, h4, h5]
  have eq1 : Real.sin a ^ 3 * (4 * Real.cos a ^ 3 - 3 * Real.cos a) + Real.cos a ^ 3 * (3 * Real.sin a - 4 * Real.sin a ^ 3) =
      3 * (Real.sin a * Real.cos a) * (Real.cos a ^ 2 - Real.sin a ^ 2) := by
    ring
  have eq2 : 3 * (Real.sin a * Real.cos a) * (Real.cos a ^ 2 - Real.sin a ^ 2) = 3 * (Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) := by
    have h6 : Real.cos a ^ 2 - Real.sin a ^ 2 = 2 * Real.cos a ^ 2 - 1 := by
      have h5 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
      linarith
    rw [h6]
  have eq3 : 3 * (Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) = (3 / 4) * (4 * (Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1)) := by
    ring
  have eq4 : 4 * (Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) = 2 * (2 * Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) := by
    ring
  have eq5 : 2 * (2 * Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) = 4 * Real.sin a * Real.cos a * (2 * Real.cos a ^ 2 - 1) := by
    ring
  have eq6 : 4 * Real.sin a * Real.cos a * (2 * Real.cos a ^ 2 - 1) = 4 * Real.sin a * Real.cos a * (2 * Real.cos a ^ 2 - 1) := by
    rfl
  rw [eq1, eq2, eq3]
  have h7 : 4 * (Real.sin a * Real.cos a) * (2 * Real.cos a ^ 2 - 1) = 4 * Real.sin a * Real.cos a * (2 * Real.cos a ^ 2 - 1) := by
    ring
  nlinarith [Real.sin_sq_add_cos_sq a, sq_nonneg (Real.sin a), sq_nonneg (Real.cos a - 1), sq_nonneg (Real.cos a ^ 2 - 1)]