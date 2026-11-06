import Mathlib

theorem algebra_5015 (x : ℝ) (h : 1.5 / 100 * x = 60) : x = 4000 := by
  have h1 : x = 4000 := by
    ring_nf at h ⊢
    linarith
  exact h1
