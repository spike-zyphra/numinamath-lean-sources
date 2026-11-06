import Mathlib

theorem algebra_96376 (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (2 * i + 1) = n * (n + 2) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top, ih]
    all_goals ring_nf <;> omega
    all_goals ring
    all_goals omega