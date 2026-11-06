import Mathlib

/-Factor $36-4x^2$ completely.-/
theorem algebra_19760 {x : ℂ} : 36 - 4 * x ^ 2 = 4 * (3 - x) * (3 + x) := by
  -- the proof is trivial
  ring_nf
