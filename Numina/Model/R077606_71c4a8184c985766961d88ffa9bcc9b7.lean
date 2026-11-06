import Mathlib

theorem number_theory_63617 (n : ℤ) (hn : n > 0) :
  (n + (n + 1) + (n + 2)) ∣ (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) := by
  use (n ^ 2 + 2 * n + 3)
  ring_nf
  <;> try omega