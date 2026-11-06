import Mathlib

theorem algebra_117146 {G : Type*} [Group G] (H1 H2 : Subgroup G)
    (h : ∀ x : G, x ∈ H1 ∨ x ∈ H2) :
    H1 = ⊤ ∨ H2 = ⊤ := by
  by_cases h1 : H1 = ⊤
  · -- Assume H1 = G
    left
    exact h1
  · -- Assume H1 ≠ G
    by_cases h2 : H2 = ⊤
    · -- Assume H2 = G
      right
      exact h2
    · -- Assume both $H_1 ≠ G$ and $H_2 ≠ G$
      have h1' : H1 ≠ ⊤ := by
        intro h1_eq
        contradiction
      have h2' : H2 ≠ ⊤ := by
        intro h2_eq
        contradiction
      have h3 : ∃ x : G, x ∉ H1 := by 
        by_contra h3
        push_neg at h3
        have h4 : H1 = ⊤ := by
          ext x
          simp [h3 x]
        contradiction
      have h4 : ∃ x : G, x ∉ H2 := by 
        by_contra h4
        push_neg at h4
        have h5 : H2 = ⊤ := by 
          ext x
          simp [h4 x]
        contradiction
      rcases h3 with ⟨g, hg⟩
      rcases h4 with ⟨h2, hh⟩
      have hg2 : g ∈ H2 := by
        have : g ∈ H1 ∨ g ∈ H2 := h g
        cases this with
        | inl h11 => 
          contradiction 
        | inr h22 => 
          exact h22 
      have hh1 : h2 ∈ H1 := by
        have : h2 ∈ H1 ∨ h2 ∈ H2 := h h2 
        cases this with
        | inl h11 => 
          exact h11 
        | inr h22 => 
          contradiction 
      have h5 : g * h2 ∈ H1 ∨ g * h2 ∈ H2 := by 
        have : g * h2 ∈ H1 ∨ g * h2 ∈ H2 := h (g * h2)
        exact this 
      cases h5 with
      | inl h7 =>
        have h77 : g * h2 ∈ H1 := h7 
        have h78 : h2 ∈ H1 := hh1 
        have h8 : (g * h2) * (h2)⁻¹ ∈ H1 := by 
          have h41 : (g * h2) ∈ H1 := h77
          have h42 : (h2)⁻¹ ∈ H1 := by 
            apply H1.inv_mem 
            exact hh1 
          have h43 : (g * h2) * (h2)⁻¹ ∈ H1 := by 
            apply H1.mul_mem 
            exact h41 
            exact h42 
          exact h43 
        have h9 : (g * h2) * (h2)⁻¹ = g := by 
          simp [mul_assoc]
        have hg2 : g ∈ H1 := by 
          rw [h9] at h8 
          exact h8 
        contradiction 
      | inr h7 =>
        have h77 : g * h2 ∈ H2 := h7 
        have h4 : g ∈ H2 := hg2 
        have h9 : (g)⁻¹ * (g * h2) ∈ H2 := by 
          have h41 : (g * h2) ∈ H2 := h77 
          have h42 : (g)⁻¹ ∈ H2 := by 
            apply H2.inv_mem 
            exact hg2 
          have h43 : (g)⁻¹ * (g * h2) ∈ H2 := by 
            apply H2.mul_mem 
            exact h42 
            exact h41 
          exact h43 
        have h10 : (g)⁻¹ * (g * h2) = h2 := by 
          simp [mul_assoc]
        have hh2 : h2 ∈ H2 := by 
          rw [h10] at h9 
          exact h9 
        contradiction