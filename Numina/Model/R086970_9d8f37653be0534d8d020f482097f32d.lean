import Mathlib

theorem algebra_276200 (x y : ℝ) : Real.sin (x - y) * Real.cos y + Real.cos (x - y) * Real.sin y = Real.sin x := by 
  have h : Real.sin (x - y) * Real.cos y + Real.cos (x - y) * Real.sin y = Real.sin ((x - y) + y) := by 
    rw [Real.sin_add]
  rw [h]
  have h2 : (x - y) + y = x := by 
    ring
  rw [h2]
  <;> ring_nf <;> simp [Real.sin_add]