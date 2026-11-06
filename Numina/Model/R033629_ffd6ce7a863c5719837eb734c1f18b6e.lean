import Mathlib

theorem number_theory_45047 {n : ℕ} (hn : n > 1) (a : Fin n → ℕ)
    (ha : ∀ i j, i < j → a i = a j + 1) (h : ∑ i, a i = 2009) :
    n = 7 → ∃ s : Finset (Fin n), s.card > 0 ∧
      (∀ i ∈ s, a i = 1996) ∧
      (∀ i ∉ s, a i = 1) := by
  intro h_eq
  -- derive contradiction with transitivity
  have h2 : n = 7 := h_eq
  have h3 := ha (⟨0, by omega⟩) (⟨1, by omega⟩) (by simp at *; all_goals omega)
  have h4 := ha (⟨0, by omega⟩) (⟨2, by omega⟩) (by simp at *; all_goals omega)
  have h5 := ha (⟨1, by omega⟩) (⟨2, by omega⟩) (by simp at *; all_goals omega)
  simp [h2] at h3 h4 h5
  all_goals
  omega