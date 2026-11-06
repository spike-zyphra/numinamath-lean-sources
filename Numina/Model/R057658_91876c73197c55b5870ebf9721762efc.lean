import Mathlib

theorem algebra_314530 {A B C : Set ℝ} :
    (B ⊆ A ∧ C ⊆ A) ↔ ((A ∩ B) ∪ (A ∩ C)) = (B ∪ C) := by
  constructor
  · -- Forward direction: If B ⊆ A and C ⊆ A, then (A ∩ B) ∪ (A ∩ C) = B ∪ C
    rintro ⟨h₁, h₂⟩
    ext x
    simp
    constructor
    · -- Assume x ∈ (A ∩ B) ∪ (A ∩ C), prove x ∈ B ∪ C
      rintro (⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩)
      · -- Case where x ∈ A ∩ B
        left
        exact hx₂
      · -- Case where x ∈ A ∩ C
        right
        exact hx₂
    · -- Assume x ∈ B ∪ C, prove x ∈ (A ∩ B) ∪ (A ∩ C)
      rintro (hx | hx)
      · -- Case where x ∈ B
        have h₃ : x ∈ A := h₁ hx
        left
        constructor
        · exact h₃
        · exact hx
      · -- Case where x ∈ C
        have h₃ : x ∈ A := h₂ hx
        right
        constructor
        · exact h₃
        · exact hx
  · -- Backward direction: If (A ∩ B) ∪ (A ∩ C) = B ∪ C, then B ⊆ A ∧ C ⊆ A
    intro h_eq
    constructor
    · -- Prove B ⊆ A
      intro b hb
      have h₂ : b ∈ (A ∩ B) ∪ (A ∩ C) := by
        rw [h_eq]
        simp
        tauto
      rcases h₂ with (h | h)
      · -- Case where b ∈ A ∩ B
        have h₃ : b ∈ A := h.1
        exact h₃
      · -- Case where b ∈ A ∩ C
        have h₃ : b ∈ A := h.1
        exact h₃
    · -- Prove C ⊆ A
      intro c hc
      have h₃ : c ∈ (A ∩ B) ∪ (A ∩ C) := by
        rw [h_eq]
        simp
        tauto
      rcases h₃ with (h | h)
      · -- Case where c ∈ A ∩ B
        have h₄ : c ∈ A := h.1
        exact h₄
      · -- Case where c ∈ A ∩ C
        have h₄ : c ∈ A := h.1
        exact h₄