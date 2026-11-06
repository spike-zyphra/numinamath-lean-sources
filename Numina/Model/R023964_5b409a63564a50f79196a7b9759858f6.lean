import Mathlib

open Real Set
open scoped Real

theorem inequalities_197670 (x y z : ℝ) (h : x + y + z = π) :
    cos (2 * x) + cos (2 * y) - cos (2 * z) ≤ 3 / 2 := by 
  have h1 : z = π - x - y := by 
    linarith
  have h2 : 2 * z = 2 * π - (2 * x + 2 * y) := by
    have : z = π - x - y := h1
    linarith
  have h3 : cos (2 * z) = cos (2 * x + 2 * y) := by
    have h4 : 2 * z = 2 * π - (2 * x + 2 * y) := h2
    rw [h4]
    have h5 : cos (2 * π - (2 * x + 2 * y)) = cos (2 * x + 2 * y) := by
      have h6 : cos (2 * π - (2 * x + 2 * y)) = cos (2 * π) * cos (2 * x + 2 * y) + sin (2 * π) * sin (2 * x + 2 * y) := by
        rw [cos_sub]
      rw [h6]
      have h8 : cos (2 * π) = 1 := by
        exact cos_two_pi
      have h9 : sin (2 * π) = 0 := by
        exact sin_two_pi
      rw [h8, h9]
      all_goals
        ring
    linarith [h5]
  have h4 : cos (2 * x + 2 * y) = cos (2 * x) * cos (2 * y) - sin (2 * x) * sin (2 * y) := by 
    rw [cos_add]
  rw [h3, h4]
  nlinarith [sq_nonneg (cos (2 * x) - cos (2 * y)), sq_nonneg (sin (2 * x) - sin (2 * y)), sq_nonneg (cos (2 * x) + cos (2 * y) - 1), sq_nonneg (sin (2 * x) + sin (2 * y)), Real.cos_sq_add_sin_sq (2 * x), Real.cos_sq_add_sin_sq (2 * y), sq_nonneg (cos (2 * x) * sin (2 * y) - sin (2 * x) * cos (2 * y)), sq_nonneg (cos (2 * x) - 1/2), sq_nonneg (cos (2 * y) - 1/2), sq_nonneg (sin (2 * x) - sin (2 * y))]