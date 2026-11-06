import Mathlib

theorem algebra_308880 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, (i * (i + 1) * (i + 3)) =
    n * (n + 1) * (n + 2) * (3 * n + 13) / 12 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    ring_nf
    <;> omega