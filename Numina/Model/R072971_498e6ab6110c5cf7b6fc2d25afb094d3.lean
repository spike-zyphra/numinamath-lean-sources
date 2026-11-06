import Mathlib

theorem algebra_111 (n : ℕ) :
  ∑ i in Finset.range n, (i+1)*(i+2)*(i+3)*(i+4) =
  (n * (n+1) * (n+2) * (n+3) * (n+4)) / 5 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf
    <;> omega