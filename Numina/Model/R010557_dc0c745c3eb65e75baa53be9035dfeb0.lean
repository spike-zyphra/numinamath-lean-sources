import Mathlib

theorem number_theory_278218 (n : ℕ) (hn : 4 ≤ n) (a : Finset ℕ)
    (ha : ∀ x ∈ a, 0 < x ∧ x < 2 * n) (h : a.card = n) :
    ∃ s : Finset ℕ, s ⊆ a ∧ 2 * n ∣ ∑ x ∈ s, x := by 
  exact ⟨∅, by simp, by simp⟩