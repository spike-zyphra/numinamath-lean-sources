import Mathlib

theorem algebra_161151 (n : ℕ) :
  ∑ k in Finset.Icc 1 n, (2 * k - 1) = n ^ 2 := by
  induction n with
  | zero =>
    simp [Finset.sum_eq_zero]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    ring_nf
    <;> omega