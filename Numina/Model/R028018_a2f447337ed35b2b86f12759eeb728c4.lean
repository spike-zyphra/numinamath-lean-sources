import Mathlib

theorem algebra_123303 (a b c : ℝ × ℝ × ℝ) :
    c • ((b • c) * a - (a • c) * b) = 0 := by
  simp [Finset.sum]
  <;> ring