import Mathlib

theorem number_theory_225305 (S : Finset ℕ) (hS : S = Finset.Icc 1 2002) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = 1001 ∧
      (∑ i ∈ T, i) % 10 > (∑ i ∈ (S \ T), i) % 10 := by
  rw [hS]
  use Finset.filter (fun x => x % 2 = 0) (Finset.Icc 1 2002)
  constructor
  · -- Show that T is a subset of S
    apply Finset.filter_subset
  constructor
  · -- Show that T has 1001 elements
    native_decide
  · -- Show that the sum condition holds
    native_decide