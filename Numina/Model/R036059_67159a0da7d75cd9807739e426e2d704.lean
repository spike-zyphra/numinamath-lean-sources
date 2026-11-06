import Mathlib

theorem number_theory_610891 (s : Finset ℕ) (hs : s = (Finset.range 7).image (fun i => 2 ^ i)) : ∀ a ≤ 127, ∃ A : Finset ℕ, A ⊆ s ∧ A.sum id = a := by
  intro a ha
  have h1 : a ≤ 127 := ha
  have h2 : a ≤ 127 := h1
  have h3 : a ≤ 127 := h1
  have h4 : a ≤ 2^7 - 1 := by
    omega
  have h5 : s = {1, 2, 4, 8, 16, 32, 64} := by
    rw [hs]
    native_decide
  have h6 : a ≤ 127 := h1
  have h7 : a ≤ 127 := h1
  have h8 : ∃ A : Finset ℕ, A ⊆ s ∧ A.sum id = a := by
    rw [h5]
    have h17 : a ≤ 127 := h1
    have h18 : a ≤ 1 + 2 + 4 + 8 + 16 + 32 + 64 := by
      omega
    have : ∃ A : Finset ℕ, A ⊆ ({1, 2, 4, 8, 16, 32, 64} : Finset ℕ) ∧ A.sum id = a := by
      have h19 : a ≤ 127 := h17
      interval_cases a <;> try { 
        native_decide 
      }
    exact this
  exact h8