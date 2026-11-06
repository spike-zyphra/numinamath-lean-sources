import Mathlib

theorem algebra_291041 (A B C : Set ℝ) :
    (B ⊆ A ∧ C ⊆ A) ↔ ((A ∩ B) ∪ (A ∩ C) = B ∪ C) := by
  constructor
  · -- Forward direction: B ⊆ A and C ⊆ A implies (A ∩ B) ∪ (A ∩ C) = B ∪ C
    rintro ⟨hB, hC⟩
    ext x
    simp
    constructor
    · -- Assume x ∈ (A ∩ B) ∪ (A ∩ C), prove x ∈ B ∪ C
      rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
      · -- Case where x ∈ A ∩ B
        left
        exact hx2
      · -- Case where x ∈ A ∩ C
        right
        exact hx2
    · -- Assume x ∈ B ∪ C, prove x ∈ (A ∩ B) ∪ (A ∩ C)
      rintro (hx | hx)
      · -- Case where x ∈ B
        have hxA : x ∈ A := by
          exact hB hx
        left
        exact ⟨hxA, hx⟩
      · -- Case where x ∈ C
        have hxA : x ∈ A := by
          exact hC hx
        right
        exact ⟨hxA, hx⟩
  · -- Backward direction: (A ∩ B) ∪ (A ∩ C) = B ∪ C implies B ⊆ A ∧ C ⊆ A
    intro heq
    constructor
    · -- Prove B ⊆ A
      intro x hx
      have h2 : x ∈ B ∪ C := by
        simp [hx]
      have h3 : x ∈ (A ∩ B) ∪ (A ∩ C) := by
        rw [heq] at *
        exact h2
      cases h3 with
      | inl h4 =>
        have h5 : x ∈ A := h4.1
        exact h5
      | inr h5 =>
        have h6 : x ∈ A := h5.1
        exact h6
    · -- Prove C ⊆ A
      intro x hx
      have h3 : x ∈ B ∪ C := by
        simp [hx]
      have h4 : x ∈ (A ∩ B) ∪ (A ∩ C) := by
        rw [heq] at *
        exact h3
      cases h4 with
      | inl h5 =>
        have h6 : x ∈ A := h5.1
        exact h6
      | inr h6 =>
        have h7 : x ∈ A := h6.1
        exact h7