import Mathlib

theorem algebra_185650 (α β : ℝ) :
    Real.sin (α / 2 + 2 * β) ^ 2 - Real.sin (α / 2 - 2 * β) ^ 2 = Real.sin α * Real.sin (4 * β) := by
  have h1 : Real.sin (α / 2 + 2 * β) ^ 2 = (1 - Real.cos (2 * (α / 2 + 2 * β)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    ring
  have h2 : Real.sin (α / 2 - 2 * β) ^ 2 = (1 - Real.cos (2 * (α / 2 - 2 * β)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    ring
  rw [h1, h2]
  have h3 : 2 * (α / 2 + 2 * β) = α + 4 * β := by 
    ring
  have h4 : 2 * (α / 2 - 2 * β) = α - 4 * β := by 
    ring
  rw [h3, h4]
  have h5 : Real.cos (α + 4 * β) = Real.cos α * Real.cos (4 * β) - Real.sin α * Real.sin (4 * β) := by
    rw [Real.cos_add]
  have h6 : Real.cos (α - 4 * β) = Real.cos α * Real.cos (4 * β) + Real.sin α * Real.sin (4 * β) := by 
    rw [Real.cos_sub]
    <;> ring
  have h7 : Real.cos (α - 4 * β) - Real.cos (α + 4 * β) = 2 * Real.sin α * Real.sin (4 * β) := by
    rw [h6, h5]
    ring
  linarith [h7]