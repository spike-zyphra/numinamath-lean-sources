import Mathlib

theorem number_theory_172887 {n : ℕ} (hn : n = ∑ i ∈ Finset.range 2002, 10^i) :
    IsSquare (n - ∑ i ∈ Finset.range 1001, 2 * 10^i) := by
  rw [hn]
  native_decide