import Mathlib

theorem algebra_256837 {f : ℝ → ℝ} {S : Finset ℝ} (hf : ∀ x, f (3 + x) = f (3 - x)) (hS₁ : S.card = 6) (hS₂ : S = {x : ℝ | f x = 0}) : S.sum id = 18 := by
  obtain ⟨A, hA⟩ := show ∃A : Finset ℝ, A = {x : ℝ | x < 3 ∧ f x = 0} by
    apply Set.Finite.exists_finset_coe
    apply Set.Finite.subset (Finset.finite_toSet S)
    rw [hS₂]; simp
  obtain ⟨B, hB⟩ := show ∃B : Finset ℝ, B = {x : ℝ | x > 3 ∧ f x = 0} by
    apply Set.Finite.exists_finset_coe
    apply Set.Finite.subset (Finset.finite_toSet S)
    rw [hS₂]; simp
  obtain ⟨C, hC⟩ := show ∃C : Finset ℝ, C = {x : ℝ | x = 3 ∧ f x = 0} by
    apply Set.Finite.exists_finset_coe
    apply Set.Finite.subset (Finset.finite_toSet S)
    rw [hS₂]; simp

  have hS₄ : S = A ∪ B ∪ C := by
    suffices (S : Set ℝ) = (A : Set ℝ) ∪ (B : Set ℝ) ∪ (C : Set ℝ) by norm_cast at this
    rw [hS₂, hA, hB, hC, Set.ext_iff]; simp
    intro x
    constructor
    · intro hx₁
      rw [←or_and_right, ←or_and_right, lt_or_lt_iff_ne]
      exact ⟨ne_or_eq x 3, hx₁⟩
    · rintro ((⟨_, _⟩ | ⟨_, _⟩) | ⟨_, _⟩)
      all_goals assumption

  have hAB : Disjoint A B := by
    suffices Disjoint (A : Set ℝ) (B : Set ℝ) by norm_cast at this
    rw [hA, hB, Set.disjoint_left]; simp
    intro x hx₁ hx₂ hx₃
    linarith

  have h₃ : ∑ x ∈ A, x = ∑ x ∈ B, (6 - x) := by
    apply Finset.sum_bij
    case i => exact (λx _ => 6 - x)
    · -- ∀ a ∈ A, 6 - a ∈ B
      suffices ∀ x ∈ (A : Set ℝ), 6 - x ∈ (B : Set ℝ) by norm_cast at this
      rw [hA, hB]; simp
      intro x hx₁ hx₂
      specialize hf (3 - x)
      field_simp at hf
      rw [←hf] at hx₂
      ring_nf at hx₂
      exact ⟨by linarith, hx₂⟩
    · -- ∀ a₁ ∈ A, ∀ a₂ ∈ A, 6 - a₁ = 6 - a₂ → a₁ = a₂
      simp
    · simp
      -- ∀ b ∈ B, ∃ a ∈ A, 6 - a = b
      suffices ∀ x ∈ (B : Set ℝ), ∃ y ∈ (A : Set ℝ), 6 - y = x by norm_cast at this
      rw [hA, hB]; simp
      intro x hx₁ hx₂
      use (6 - x); simp
      specialize hf (3 - x)
      field_simp at hf
      rw [←hf] at hx₂
      ring_nf at hx₂
      exact ⟨by linarith, hx₂⟩
    · -- ∀ a ∈ A, a = 6 - (6 - a)
      simp

  have h₄ : A.card = B.card := by
    apply Finset.card_bij
    case i => exact (λx _ => 6 - x)
    · -- ∀ a ∈ A, 6 - a ∈ B
      suffices ∀ x ∈ (A : Set ℝ), 6 - x ∈ (B : Set ℝ) by norm_cast at this
      rw [hA, hB]; simp
      intro x hx₁ hx₂
      specialize hf (3 - x)
      field_simp at hf
      rw [←hf] at hx₂
      ring_nf at hx₂
      exact ⟨by linarith, hx₂⟩
    · -- ∀ a₁ ∈ A, ∀ a₂ ∈ A, 6 - a₁ = 6 - a₂ → a₁ = a₂
      simp
    · simp
      -- ∀ b ∈ B, ∃ a ∈ A, 6 - a = b
      suffices ∀ x ∈ (B : Set ℝ), ∃ y ∈ (A : Set ℝ), 6 - y = x by norm_cast at this
      rw [hA, hB]; simp
      intro x hx₁ hx₂
      use (6 - x); simp
      specialize hf (3 - x)
      field_simp at hf
      rw [←hf] at hx₂
      ring_nf at hx₂
      exact ⟨by linarith, hx₂⟩

  have hABC : Disjoint (A ∪ B) C := by
    suffices Disjoint ((A : Set ℝ) ∪ (B : Set ℝ)) (C : Set ℝ) by norm_cast at this
    rw [hA, hB, hC, Set.disjoint_left]; simp
    rintro _ (⟨_, _⟩ | ⟨_, _⟩) _
    all_goals linarith

  rw [←Finset.card_union_eq_card_add_card] at hABC
  rw [Finset.card_union_eq_card_add_card.mpr hAB, ←hS₄, hS₁, h₄] at hABC

  have hC₁ : C = ∅ := by
    have : (C : Set ℝ) = ∅ ∨ (C : Set ℝ) = {3} := by
      apply Set.subset_singleton_iff_eq.mp
      rw [hC]; simp
    norm_cast at this
    rcases this with (rfl | hC)
    · rfl
    · rw [hC] at hABC
      simp at hABC
      omega

  rw [hC₁] at hS₄ hABC
  simp at hS₄ hABC
  rw [hS₄, Finset.sum_union hAB]; simp
  rw [h₃, ←Finset.sum_add_distrib]
  suffices B.card = 3 by
    simp
    rw [this]
    norm_num
  linarith
