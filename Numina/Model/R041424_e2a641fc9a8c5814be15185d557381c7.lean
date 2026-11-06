import Mathlib

theorem algebra_257085 (α β : ℝ) :
    1 - Real.cos (β - α) + Real.cos α - Real.cos β =
    4 * Real.cos (α / 2) * Real.sin (β / 2) * Real.sin ((β - α) / 2) := by
  have h1 : Real.cos (β - α) = Real.cos β * Real.cos α + Real.sin β * Real.sin α := by
    rw [Real.cos_sub]

  have h2 : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    have h2 : Real.cos α = Real.cos (2 * (α / 2)) := by ring_nf
    rw [h2]
    rw [Real.cos_two_mul]

  have h3 : Real.cos β = 2 * Real.cos (β / 2) ^ 2 - 1 := by
    have h3 : Real.cos β = Real.cos (2 * (β / 2)) := by ring_nf
    rw [h3]
    rw [Real.cos_two_mul]

  have h4 : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
    have h4 : Real.sin β = Real.sin (2 * (β / 2)) := by ring_nf
    rw [h4]
    rw [Real.sin_two_mul]

  have h5 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    have h5 : Real.sin α = Real.sin (2 * (α / 2)) := by ring_nf
    rw [h5]
    rw [Real.sin_two_mul]

  have h6 : Real.sin ((β - α) / 2) = Real.sin (β / 2 - α / 2) := by ring_nf

  have h7 : Real.sin (β / 2 - α / 2) = Real.sin (β / 2) * Real.cos (α / 2) - Real.cos (β / 2) * Real.sin (α / 2) := by
    rw [Real.sin_sub]

  have h8 : Real.sin ((β - α) / 2) = Real.sin (β / 2) * Real.cos (α / 2) - Real.cos (β / 2) * Real.sin (α / 2) := by
    rw [h6, h7]

  rw [h1, h2, h3, h4, h5, h8]
  have h9 : Real.sin (β / 2) ^ 2 + Real.cos (β / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (β / 2)
  have h10 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α / 2)
  ring_nf at *
  <;> simp [Real.sin_sq, Real.cos_sq, h9, h10] at *
  <;> ring