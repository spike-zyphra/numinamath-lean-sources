import Mathlib

theorem algebra_12636 {A B C : Set ℝ} :
  (B ⊆ A ∧ C ⊆ A) ↔ ((A ∩ B) ∪ (A ∩ C)) = B ∪ C := by
  constructor
  · -- Assume $B \subseteq A$ and $C \subseteq A$, prove $(A \cap B) \cup (A \cap C) = B \cup C$.
    rintro ⟨hB, hC⟩
    have h1 : A ∩ B = B := Set.inter_eq_right.mpr hB
    have h2 : A ∩ C = C := Set.inter_eq_right.mpr hC
    rw [h1, h2]
  · -- Assume $(A \cap B) \cup (A \cap C) = B \cup C$, prove $B \subseteq A ∧ C \subseteq A$.
    intro heq
    constructor
    · -- Show that $B \subseteq A$.
      intro x hx
      have h1 : x ∈ B ∪ C := by 
        have h1 : x ∈ B := hx
        simp [h1]
      have h2 : x ∈ (A ∩ B) ∪ (A ∩ C) := by 
        rw [heq] at *
        exact h1
      cases h2 with
      | inl h3 =>
        have h4 : x ∈ A := h3.1
        exact h4
      | inr h3 =>
        have h4 : x ∈ A := h3.1
        exact h4
    · -- Show that $C \subseteq A$.
      intro x hx
      have h1 : x ∈ B ∪ C := by 
        have h1 : x ∈ C := hx
        simp [h1]
      have h2 : x ∈ (A ∩ B) ∪ (A ∩ C) := by
        rw [heq] at *
        exact h1
      cases h2 with
      | inl h3 =>
        have h4 : x ∈ A := h3.1
        exact h4
      | inr h3 =>
        have h4 : x ∈ A := h3.1
        exact h4