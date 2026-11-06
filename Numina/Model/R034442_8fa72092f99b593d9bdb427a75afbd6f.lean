import Mathlib

theorem inequalities_96524 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : -1 < y ∧ y < 0) (hz : 1 < z ∧ z < 2) : 0 < y + z := by
  have h1 : -1 < y := hy.1
  have h2 : 1 < z := hz.1
  linarith