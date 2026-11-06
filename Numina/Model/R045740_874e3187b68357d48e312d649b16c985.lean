import Mathlib

theorem number_theory_310843 (S : Finset ℕ) (hS : S = {1, 2, 3}) :
    ∑ x ∈ S, x = ∏ x ∈ S, x ∧ S.card ≥ 2 := by
  rw [hS]
  constructor
  · -- Show that sum equals product
    native_decide
  · -- Show that the cardinality is at least 2
    native_decide