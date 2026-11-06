import Mathlib

theorem calculus_16242 (x y : ℝ) : Real.sin (x - y) * Real.cos y + Real.cos (x - y) * Real.sin y = Real.sin x := by 
  have h : Real.sin (x - y) * Real.cos y + Real.cos (x - y) * Real.sin y = Real.sin ((x - y) + y) := by 
    rw [Real.sin_add]
    all_goals ring
  have h2 : (x - y) + y = x := by 
    ring
  rw [h, h2]