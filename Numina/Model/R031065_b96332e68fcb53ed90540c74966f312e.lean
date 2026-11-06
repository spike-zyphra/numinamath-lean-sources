import Mathlib

theorem number_theory_278339 (n : ℕ) :
    7 ^ ⌊n / 3⌋₊ ∣ ∑ k ∈ Finset.range 3, (2 * Real.sin ((k + 1) * Real.pi / 7)) ^ (2 * n) := by
  norm_num [Finset.sum_range_succ]