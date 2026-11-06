import Mathlib

theorem algebra_219372 (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, i^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by linarith)]
    rw [ih]
    ring_nf
    omega