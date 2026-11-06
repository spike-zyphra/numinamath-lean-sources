import Mathlib

theorem number_theory_597555 (n : ℕ) (hn : 1 < n) :
    ∃ i j, 1 / n = ∑ k ∈ Finset.Icc i j, 1 / (k * (k + 1)) := by
  use 0
  use 0
  simp at *
  all_goals omega