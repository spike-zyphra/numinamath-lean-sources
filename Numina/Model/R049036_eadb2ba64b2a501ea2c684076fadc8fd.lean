import Mathlib

theorem number_theory_209548 : ∃ n, n > 0 ∧ ∃ s : Finset ℕ, ∑ i ∈ s, (2 ^ (i + 100) - 1) = 2 ^ n - 1 := by
  use 200
  constructor
  · -- Show that 200 > 0
    norm_num
  · -- Show the existence of a set `s` such that the sum equals $2^{200} - 1$
    use {100}
    native_decide