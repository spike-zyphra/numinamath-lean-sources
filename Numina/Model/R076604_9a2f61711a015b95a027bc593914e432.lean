import Mathlib

theorem algebra_235801 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, i^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    ring_nf
    <;> omega