import Mathlib

theorem algebra_278583 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, i^3 = n^2 * (n + 1)^2 / 4 := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    ring_nf
    <;> omega