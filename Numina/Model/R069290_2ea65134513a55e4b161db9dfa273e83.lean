import Mathlib

theorem algebra_40293 (n : ℕ) (hn : n > 0) :
    ∑ i in Finset.range n, (i + 1) * (i + 4) = n * (n + 1) * (n + 5) / 3 := by
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [Finset.sum_range_succ, ih] at *
      ring_nf
      omega