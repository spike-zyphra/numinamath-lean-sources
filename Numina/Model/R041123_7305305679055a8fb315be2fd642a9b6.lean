import Mathlib

theorem algebra_185518 (α x : ℝ) :
    Real.sin α * Real.sin (x - α) + Real.sin ((x / 2) - α) ^ 2 =
    Real.sin (x / 2) ^ 2 := by
  have h1 : Real.sin (x - α) = Real.sin x * Real.cos α - Real.cos x * Real.sin α := by 
    rw [Real.sin_sub]
  have h2 : Real.sin ((x / 2) - α) ^ 2 = (1 - Real.cos (x - 2 * α)) / 2 := by 
    have h3 : Real.sin ((x / 2) - α) ^ 2 = (1 - Real.cos (2 * ((x / 2) - α))) / 2 := by 
      rw [Real.sin_sq_eq_half_sub]
      <;> ring
    have h4 : 2 * ((x / 2) - α) = x - 2 * α := by 
      ring
    rw [h3]
    rw [h4]
  have h3 : Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by 
    have h4 : Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring_nf
    linarith
  rw [h1, h2, h3]
  have h4 : Real.cos (x - 2 * α) = Real.cos x * Real.cos (2 * α) + Real.sin x * Real.sin (2 * α) := by
    rw [Real.cos_sub]
  have h5 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_two_mul]
  have h6 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h4, h5, h6]
  ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq]
  <;> ring