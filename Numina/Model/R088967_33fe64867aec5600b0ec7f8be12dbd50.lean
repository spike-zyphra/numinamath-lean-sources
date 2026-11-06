import Mathlib

theorem algebra_11789 (k : ℝ) :
    ∃ a b, ∀ x, x^2 - 16 * x + k = (a * x + b)^2 ↔ k = 64 := by
  use 1
  use -8
  intro x
  constructor
  · -- Assume $x^2 - 16x + k = (1 \cdot x + (-8))^2$, then $k = 64$.
    intro h
    ring_nf at h
    linarith
  · -- Assume $k = 64$, then $x^2 - 16 x + k = (1 \cdot x + (-8))^2$.
    intro h
    rw [h]
    ring_nf