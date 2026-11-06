import Mathlib

open Real Set
open scoped Real

theorem algebra_274619 (α : ℝ) (hα : ∀ k : ℤ, α ≠ 1/2 * k * π) :
    (sin α + tan α) / (cos α + 1/tan α) > 0 := by

  have h1 : sin α ≠ 0 := by 
    by_contra h
    have h2 : ∃ k : ℤ, α = 1/2 * k * π := by
      have h3 : sin α = 0 := h
      have h4 : ∃ m : ℤ, α = m * π := by 
        rw [sin_eq_zero_iff] at h3 
        rcases h3 with ⟨m, hm⟩ 
        refine' ⟨m, ?_⟩ 
        all_goals linarith 
      rcases h4 with ⟨m, hm⟩ 
      use 2 * m 
      all_goals 
        field_simp at hm ⊢ 
        <;> nlinarith 
    rcases h2 with ⟨k, hk⟩ 
    have h3 : α ≠ 1/2 * k * π := hα k 
    contradiction

  have h2 : cos α ≠ 0 := by 
    by_contra h 
    have h3 : cos α = 0 := h 
    have h4 : ∃ m : ℤ, α = (m + 1/2) * π := by 
      rw [cos_eq_zero_iff] at h3 
      rcases h3 with ⟨m, hm⟩ 
      use m 
      all_goals linarith 
    rcases h4 with ⟨m, hm⟩ 
    have h5 : ∃ k' : ℤ, α = 1/2 * k' * π := by 
      use 2 * m + 1 
      all_goals 
        field_simp at hm ⊢ 
        <;> ring_nf at hm ⊢ 
        <;> nlinarith 
    rcases h5 with ⟨k', hk'⟩ 
    have h3 : α ≠ 1/2 * k' * π := hα k' 
    contradiction

  have htan : tan α = sin α / cos α := by 
    rw [tan_eq_sin_div_cos]

  have h41 : (sin α + tan α) / (cos α + 1 / tan α) = (sin α ^ 2 * (cos α + 1)) / (cos α ^ 2 * (sin α + 1)) := by 
    rw [htan] 
    have hcos : cos α ≠ 0 := h2 
    have hsin : sin α ≠ 0 := h1 
    field_simp [hcos, hsin] 
    <;> ring_nf <;> 
      field_simp [hcos, hsin] 
    <;> nlinarith

  have h31 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  rw [h41] 
  have h42 : sin α ^ 2 * (cos α + 1) > 0 := by 
    have hsin2_pos : sin α ^ 2 > 0 := by 
      have hsin_ne : sin α ≠ 0 := h1 
      have : sin α ^ 2 > 0 := by 
        apply pow_two_pos_of_ne_zero 
        exact hsin_ne 
      linarith 
    have hcos1_pos : cos α + 1 > 0 := by 
      by_contra h 
      push_neg at h 
      have hcos_le : cos α ≤ -1 := by 
        nlinarith 
      have hcos_eq : cos α = -1 := by 
        nlinarith [Real.cos_le_one α, Real.neg_one_le_cos α, sq_nonneg (cos α + 1)] 
      have hsin_eq : sin α ^ 2 = 0 := by 
        rw [hcos_eq] at h31 
        nlinarith 
      have hsin0 : sin α = 0 := by 
        nlinarith 
      contradiction 
    nlinarith

  have h43 : cos α ^ 2 * (sin α + 1) > 0 := by 
    have hcos2_pos : cos α ^ 2 > 0 := by 
      have hcos_ne : cos α ≠ 0 := h2 
      have : cos α ^ 2 > 0 := by 
        apply pow_two_pos_of_ne_zero 
        exact hcos_ne 
      linarith 
    have hsin1_pos : sin α + 1 > 0 := by 
      by_contra h 
      push_neg at h 
      have hsin_le : sin α ≤ -1 := by 
        nlinarith 
      have hsin_eq : sin α = -1 := by 
        nlinarith [Real.sin_le_one α, Real.neg_one_le_sin α, sq_nonneg (sin α + 1)] 
      have hsin_eq : sin α = -1 := by 
        nlinarith 
      have hcos_eq : cos α ^ 2 = 0 := by 
        rw [hsin_eq] at h31 
        nlinarith 
      have hcos0 : cos α = 0 := by 
        nlinarith 
      contradiction 
    nlinarith

  apply div_pos 
  · exact h42 
  · exact h43