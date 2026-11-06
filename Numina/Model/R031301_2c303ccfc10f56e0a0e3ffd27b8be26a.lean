import Mathlib

theorem algebra_273885 {A B X : Set ℝ} (hA : A ∪ B ∪ X = A ∪ B) (hB : A ∩ X = B ∩ X)
    (hC : B ∩ X = A ∩ B) : X = A ∩ B := by
  have h1 : X ⊆ A ∪ B := by
    have h2 : A ∪ B ∪ X = A ∪ B := hA 
    have h3 : X ⊆ A ∪ B := by 
      have h4 : X ⊆ A ∪ B ∪ X := by
        intro x hx
        simp at hx ⊢
        tauto 
      have h5 : A ∪ B ∪ X = A ∪ B := h2 
      rw [h5] at h4 
      exact h4 
    exact h3
  have h5 : A ∩ B ⊆ X := by 
    have h6 : B ∩ X = A ∩ B := hC 
    have h7 : A ∩ B = B ∩ X := by 
      rw [h6]
    have h8 : A ∩ B ⊆ X := by
      rw [h7] 
      simp
    exact h8
  have h7 : X ⊆ B := by
    intro x hx
    have h8 : x ∈ X := hx 
    have h9 : x ∈ A ∪ B := by
      have h10 : x ∈ X := hx 
      have h11 : x ∈ A ∪ B ∪ X := by 
        simp [h10]
      have h12 : A ∪ B ∪ X = A ∪ B := hA 
      rw [h12] at h11 
      exact h11 
    rcases h9 with (ha | hb)
    · 
      have h10 : x ∈ A ∩ X := by 
        exact ⟨ha, hx⟩
      have h11 : A ∩ X = A ∩ B := by 
        have h15 : A ∩ X = B ∩ X := by 
          exact hB
        have h16 : B ∩ X = A ∩ B := by 
          exact hC
        rw [h16] at h15 
        exact h15
      have h12 : x ∈ A ∩ B := by 
        have h13 : x ∈ A ∩ X := h10 
        have h14 : A ∩ X = A ∩ B := h11 
        rw [h14] at h13 
        exact h13 
      have h13 : x ∈ B := by 
        simp at h12 ⊢ 
        tauto 
      exact h13 
    · 
      exact hb
  have h8 : X ⊆ A := by
    intro x hx
    have h9 : x ∈ X := hx 
    have h10 : x ∈ A ∪ B := by
      have h11 : x ∈ X := hx 
      have h12 : x ∈ A ∪ B ∪ X := by 
        simp [h11]
      have h13 : A ∪ B ∪ X = A ∪ B := hA 
      rw [h13] at h12 
      exact h12 
    rcases h10 with (ha | hb)
    · 
      exact ha 
    · 
      have h12 : x ∈ B ∩ X := by 
        exact ⟨hb, hx⟩
      have h13 : B ∩ X = A ∩ B := hC 
      have h14 : x ∈ A ∩ B := by 
        rw [h13] at h12 
        exact h12 
      have h15 : x ∈ A := by 
        simp at h14 ⊢ 
        tauto 
      exact h15 
  have h9 : X ⊆ A ∩ B := by
    intro y hy
    have h11 : y ∈ A ∪ B := by
      have h12 : y ∈ X := hy 
      have h13 : y ∈ A ∪ B ∪ X := by simp [h12] 
      have h14 : A ∪ B ∪ X = A ∪ B := hA 
      rw [h14] at h13 
      exact h13 
    rcases h11 with (hA1 | hB1)
    · -- Case y ∈ A
      have h10 : y ∈ A ∩ X := by 
        exact ⟨hA1, hy⟩ 
      have h11 : A ∩ X = A ∩ B := by 
        have h15 : A ∩ X = B ∩ X := by 
          exact hB 
        have h16 : B ∩ X = A ∩ B := by 
          exact hC 
        rw [h16] at h15 
        exact h15 
      rw [h11] at h10 
      exact h10 
    · -- Case y ∈ B
      have h10 : y ∈ B ∩ X := by 
        exact ⟨hB1, hy⟩ 
      have h11 : B ∩ X = A ∩ B := hC 
      rw [h11] at h10 
      exact h10 
  exact Set.Subset.antisymm h9 h5