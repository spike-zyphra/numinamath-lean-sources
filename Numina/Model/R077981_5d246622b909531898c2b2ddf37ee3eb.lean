import Mathlib

theorem algebra_328155 {f g : Polynomial ℝ} (hf : f = 3 * X ^ 4 + X ^ 3 - 4 * X ^ 2 - 17 * X + 5)
    (hg : g = X ^ 2 + X + 1) :
    ∃ q r, f = g * q + r ∧ r = -10 * X + 10 := by
  use 3 * X ^ 2 - 2 * X - 5
  use -10 * X + 10
  constructor
  · -- Show that f = g * q + r
    rw [hf, hg]
    ring_nf
  · -- Show that r = -10 * x + 10
    rfl