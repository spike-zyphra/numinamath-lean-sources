import Mathlib

open Real Set
open scoped Real

theorem algebra_156176 {α β : ℝ} (h : cos (α + β) = 0) :
    sin (α + 2 * β) = sin α := by
  have h1 : sin (α + 2 * β) = sin (α + β) * cos β := by 
    have h2 : sin (α + 2 * β) = sin ((α + β) + β) := by 
      ring_nf
    rw [h2]
    rw [sin_add]
    simp [h]
  
  have h2 : sin α = sin (α + β) * cos β := by 
    have h3 : sin α = sin ((α + β) - β) := by 
      ring_nf 
    rw [h3]
    rw [sin_sub]
    simp [h]
  
  rw [h1, h2]