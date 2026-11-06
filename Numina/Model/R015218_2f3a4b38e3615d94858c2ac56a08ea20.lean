import Mathlib

theorem algebra_153894 (α : ℝ) :
    (Real.sin (7 * α) - Real.sin (5 * α)) / (Real.sin (7 * α) + Real.sin (5 * α)) =
    Real.tan α * 1 / Real.tan (6 * α) := by
  have h1 : Real.sin (7 * α) - Real.sin (5 * α) = 2 * Real.cos (6 * α) * Real.sin α := by 
    rw [show 7 * α = 6 * α + α by ring, show 5 * α = 6 * α - α by ring]
    rw [Real.sin_add, Real.sin_sub]
    ring
  have h2 : Real.sin (7 * α) + Real.sin (5 * α) = 2 * Real.sin (6 * α) * Real.cos α := by
    rw [show 7 * α = 6 * α + α by ring, show 5 * α = 6 * α - α by ring]
    rw [Real.sin_add, Real.sin_sub]
    ring
  rw [h1, h2]
  have htan : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  have htan6 : Real.tan (6 * α) = Real.sin (6 * α) / Real.cos (6 * α) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan, htan6]
  field_simp
  <;> ring_nf <;> field_simp <;> ring