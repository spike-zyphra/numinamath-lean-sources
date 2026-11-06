import Mathlib

theorem number_theory_247673 : ∃ n, 2018 ∈ {x | Even x ∧ x ∈ Finset.Icc (n * (3 * n - 2)) (n * (3 * n - 2) + 2 * n - 1)} := by
  use 26
  constructor
  · -- Show that 2018 is even
    exact Nat.even_iff.2 (by norm_num)
  · -- Show that 2018 is in the interval [1976, 2027]
    native_decide