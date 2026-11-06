import Mathlib

theorem algebra_103637 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by linarith)]
    rw [ih]
    ring_nf
    <;> omega