import Mathlib

theorem algebra_299170 (x y α β : ℝ) :
    (x * Real.cos (2 * α) + y * Real.sin (2 * α) - 1) *
    (x * Real.cos (2 * β) + y * Real.sin (2 * β) - 1) -
    ((x * Real.cos (α + β) + y * Real.sin (α + β)) - Real.cos (α - β))^2 =
    (1 - x^2 - y^2) * (Real.sin (α - β))^2 := by 
  have h1 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  have h2 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]
  have h3 : Real.cos (2 * β) = 2 * Real.cos β ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  have h4 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by 
    rw [Real.sin_two_mul]
  have h5 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by 
    rw [Real.cos_add]
  have h6 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [Real.sin_add]
  have h7 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by 
    rw [Real.cos_sub]
  have h8 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := by 
    rw [Real.sin_sub]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring_nf 
  <;> simp [Real.sin_sq, Real.cos_sq]
  <;> ring