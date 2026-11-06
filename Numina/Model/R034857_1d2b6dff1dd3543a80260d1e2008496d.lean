import Mathlib

theorem algebra_238220 (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ)
    (h₀ : ∀ i, d i > 0) (h₁ : ∀ i, i = d i) :
    ∃ c, ∀ p : Equiv.Perm (Fin n), c = ∑ i, (p i) * (d i) := by

  have h2 := h₁ (⟨0, by omega⟩)
  simp at h2 
  have h3 := h₀ (⟨0, by omega⟩)
  linarith [h3, h2]