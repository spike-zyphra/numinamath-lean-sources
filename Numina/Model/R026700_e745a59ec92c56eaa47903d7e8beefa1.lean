import Mathlib

theorem number_theory_92142 (S : Finset ℕ) (hS : S.Nonempty ∧ ∀ x ∈ S, x > 0) :
    ∀ N, ∃ n > N, ¬∃! m : Finset ℕ, Odd m.card ∧ ∑ i ∈ m, i = n ∧ ∀ i ∈ m, i ∈ S := by
  intro N
  use (N + 1 + ∑ x in S, x) + 1
  constructor
  · -- Show n > N
    have h1 : (∑ x in S, x) ≥ 0 := by
      apply Finset.sum_nonneg
      intro x hx
      have h2 : x > 0 := (hS.right) x hx
      omega
    omega
  · -- Show not clean
    intro h
    rcases h with ⟨m, ⟨hm1, hm2⟩⟩
    have h1 : Odd m.card := hm1.1
    have h2 : ∑ i ∈ m, i = (N + 1 + ∑ x in S, x) + 1 := hm1.2.1
    have h3 : ∀ i ∈ m, i ∈ S := hm1.2.2
    have h4 : ∑ i ∈ m, i ≤ ∑ x in S, x := by
      have h3' : ∀ i ∈ m, i ∈ S := h3
      have h5 : m ⊆ S := by
        intro x hx
        specialize h3' x (show x ∈ m by exact hx)
        tauto
      have h6 : ∑ i in m, i ≤ ∑ i in S, i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h5
        intro x hx
        simp
      linarith
    have h7 : ∑ x in S, x ≥ 0 := by
      apply Finset.sum_nonneg
      intro x hx
      have h2 : x > 0 := (hS.right) x hx
      omega
    omega