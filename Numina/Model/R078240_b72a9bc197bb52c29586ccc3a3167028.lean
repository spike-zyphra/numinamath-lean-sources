import Mathlib

theorem algebra_147962 (n : ℕ) :
    ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf
    omega