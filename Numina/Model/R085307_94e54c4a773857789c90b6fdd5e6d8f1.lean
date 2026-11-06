import Mathlib

def P (n : ℕ) : Prop :=
  ∑ i in Finset.range n, (2 * i + 1) = n ^ 2

theorem algebra_300409 (n : ℕ) : P n := by
  unfold P
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [add_sq]
    <;> ring_nf <;> omega