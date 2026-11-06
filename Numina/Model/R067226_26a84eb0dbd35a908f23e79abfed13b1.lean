import Mathlib

open Real Set
open scoped Real

theorem algebra_295015 (α β : ℝ) (h : α + β ≤ π) :
    sin α + sin β = 2 * sin ((α + β) / 2) * cos ((α - β) / 2) := by
  have h1 : sin α = sin ((α + β) / 2 + (α - β) / 2) := by
    ring_nf
  have h2 : sin β = sin ((α + β) / 2 - (α - β) / 2) := by
    ring_nf
  rw [h1, h2]
  rw [sin_add, sin_sub]
  ring_nf
  <;> simp [sin_add, sin_sub, mul_add, add_mul]
  <;> ring_nf
  <;> simp [sin_add, sin_sub, mul_add, add_mul]
  <;> ring_nf
  <;> simp [sin_add, sin_sub, mul_add, add_mul]
  <;> ring_nf