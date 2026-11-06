import Mathlib

theorem number_theory_165742 (M : Finset ℕ) (hM : M.card = 2018)
    (hM1 : ∀ x ∈ M, ¬ 2018 ∣ x) :
    ∃ T ⊆ M, 2018 ∣ ∑ x ∈ T, x := by 
  use ∅
  constructor
  · -- Show that ∅ ⊆ M
    simp
  · -- Show that 2018 divides the sum of elements in ∅
    simp