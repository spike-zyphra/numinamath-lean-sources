import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185604 (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ × ℝ)
  (hf : f = λ t => (a * (t - sin t), a * (1 - cos t))) :
  ∃ x y, x = 0 ∧ y = -1 / 3 := by 
  exact ⟨0, -1 / 3, rfl, rfl⟩