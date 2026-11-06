import Mathlib

open Real Set
open scoped Real

theorem algebra_263779 (α : ℝ) (hα : ¬ ∃ k : ℤ, α = k * π / 2) :
    (sin α + tan α) / (cos α + 1 / tan α) > 0 := by
  have h1 : sin α ≠ 0 := by
    by_contra h
    have h3 : ∃ k : ℤ, α = k * π / 2 := by
      have h4 : sin α = 0 := by linarith [h]
      have h5 : ∃ k : ℤ, α = k * π := by 
        rw [Real.sin_eq_zero_iff] at h4
        rcases h4 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        linarith [hk]
      rcases h5 with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      field_simp at hk ⊢
      <;> linarith [Real.pi_pos]
    contradiction

  have h2 : cos α ≠ 0 := by
    by_contra h
    have h3 : ∃ k : ℤ, α = k * π / 2 := by
      have h4 : cos α = 0 := by linarith [h]
      have h5 : ∃ k : ℤ, α = k * π + π / 2 := by 
        rw [Real.cos_eq_zero_iff] at h4
        rcases h4 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        linarith [hk]
      rcases h5 with ⟨k, hk⟩
      refine ⟨2 * k + 1, ?_⟩
      field_simp at hk ⊢
      <;> nlinarith [Real.pi_pos, hk]
    contradiction

  have h3 : (sin α + tan α) / (cos α + 1 / tan α) = 
          sin α ^ 2 * (cos α + 1) / (cos α ^ 2 * (sin α + 1)) := by 
    have htan : tan α = sin α / cos α := by 
      rw [tan_eq_sin_div_cos]
    rw [htan]
    have htan2 : sin α / cos α = sin α / cos α := by rfl
    field_simp [h1, h2]
    <;> ring_nf <;> field_simp [h1, h2]
    <;> ring_nf <;> field_simp [h1, h2]
    <;> ring
  have h4 : sin α ^ 2 > 0 := by
    have h5 : sin α ≠ 0 := h1
    have h6 : sin α ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero 
      exact h5
    linarith
  have h5 : cos α ^ 2 > 0 := by
    have h6 : cos α ≠ 0 := h2
    have h7 : cos α ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero 
      exact h6
    linarith
  have h7 : sin α ^ 2 * (cos α + 1) > 0 := by
    have h8 : sin α ^ 2 > 0 := by nlinarith [sq_pos_of_ne_zero h1]
    have h9 : cos α + 1 > 0 := by
      by_contra h
      push_neg at h
      have h10 : cos α ≤ -1 := by linarith
      have h11 : cos α ^ 2 ≥ 1 := by nlinarith [sq_nonneg (cos α + 1)]
      nlinarith [Real.sin_sq_add_cos_sq α, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]
    nlinarith
  have h8 : cos α ^ 2 * (sin α + 1) > 0 := by
    have h9 : cos α ^ 2 > 0 := by nlinarith [sq_pos_of_ne_zero h2]
    have h10 : sin α + 1 > 0 := by
      by_contra h
      push_neg at h
      have h11 : sin α ≤ -1 := by linarith
      have h12 : sin α ^ 2 ≥ 1 := by nlinarith [sq_nonneg (sin α + 1)]
      nlinarith [Real.sin_sq_add_cos_sq α, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]
    nlinarith
  rw [h3]
  apply div_pos
  all_goals nlinarith [h7, h8, h4, h5, Real.sin_sq_add_cos_sq α]