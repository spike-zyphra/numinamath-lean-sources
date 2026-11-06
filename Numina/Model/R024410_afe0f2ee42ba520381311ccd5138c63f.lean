import Mathlib

theorem algebra_299130 {A B α : ℝ} :
    Real.cos (A - α) ^ 2 + Real.cos (B - α) ^ 2 -
    2 * Real.cos (A - B) * Real.cos (A - α) * Real.cos (B - α) =
    Real.sin (A - B) ^ 2 := by 
  have h1 : Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B := by 
    rw [Real.cos_sub]
  have h2 : Real.cos (A - α) = Real.cos A * Real.cos α + Real.sin A * Real.sin α := by 
    rw [Real.cos_sub]
  have h3 : Real.cos (B - α) = Real.cos B * Real.cos α + Real.sin B * Real.sin α := by 
    rw [Real.cos_sub]
  have h4 : Real.sin (A - B) = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by 
    rw [Real.sin_sub]
  rw [h1, h2, h3, h4]
  ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq]
  <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
  <;> ring