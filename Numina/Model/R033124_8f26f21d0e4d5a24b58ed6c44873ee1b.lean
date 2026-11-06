import Mathlib

open Real Set
open scoped Real

theorem algebra_118220 (α : ℝ) (hα : ¬ ∃ k : ℤ, α = k * π / 2) :
    (sin α + tan α) / (cos α + 1 / tan α) > 0 := by
  have h1 : sin α ≠ 0 := by
    by_contra h
    have h3 : ∃ k : ℤ, α = k * π / 2 := by
      have h4 : sin α = 0 := by linarith
      rw [Real.sin_eq_zero_iff] at h4
      rcases h4 with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      field_simp at hk ⊢
      linarith
    contradiction
  have h2 : cos α ≠ 0 := by
    by_contra h
    have h3 : ∃ k : ℤ, α = k * π / 2 := by
      have h4 : cos α = 0 := by linarith
      rw [Real.cos_eq_zero_iff] at h4
      rcases h4 with ⟨k, hk⟩
      refine ⟨2 * k + 1, ?_⟩
      field_simp at hk ⊢
      linarith
    contradiction
  have htan : tan α = sin α / cos α := by rw [tan_eq_sin_div_cos]
  have h3 : sin α + tan α = sin α * (cos α + 1) / cos α := by
    rw [htan]
    have h4 : cos α ≠ 0 := h2
    field_simp [h4]
    all_goals nlinarith [Real.sin_sq_add_cos_sq α]
  have h4 : cos α + 1 / tan α = cos α * (sin α + 1) / sin α := by
    rw [htan]
    have h5 : sin α ≠ 0 := h1
    field_simp [h5]
    all_goals nlinarith [Real.sin_sq_add_cos_sq α]
  rw [h3, h4]
  have h5 : sin α ^ 2 > 0 := by
    have h8 : sin α ≠ 0 := h1
    nlinarith [sq_pos_of_ne_zero (show sin α ≠ 0 by exact h8)]
  have h6 : cos α ^ 2 > 0 := by
    have h8 : cos α ≠ 0 := h2
    nlinarith [sq_pos_of_ne_zero (show cos α ≠ 0 by exact h8)]
  have h7 : cos α + 1 > 0 := by
    have h8 : cos α > -1 := by
      by_contra h
      push_neg at h
      have h9 : cos α = -1 := by
        nlinarith [Real.neg_one_le_cos α, Real.cos_le_one α, sq_nonneg (sin α ^ 2), sq_nonneg (cos α + 1), Real.sin_sq_add_cos_sq α]
      -- If `cos α = -1`, then `sin α ^ 2 = 1 - cos α ^ 2 = 0`, so `sin α = 0`
      have h10 : sin α ^ 2 = 0 := by
        have h13 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        rw [show cos α = -1 by linarith [h9]] at h13
        nlinarith
      have h11 : sin α = 0 := by nlinarith [h10]
      -- This contradicts `h1`
      contradiction
    nlinarith
  have h8 : sin α + 1 > 0 := by
    have h9 : sin α > -1 := by
      by_contra h
      push_neg at h
      have h10 : sin α = -1 := by
        nlinarith [Real.neg_one_le_sin α, Real.sin_le_one α, sq_nonneg (cos α ^ 2), sq_nonneg (sin α + 1), Real.sin_sq_add_cos_sq α]
      -- If `sin α = -1`, then `cos α ^ 2 = 1 - sin α ^ 2 = 0`, so `cos α = 0`
      have h11 : cos α ^ 2 = 0 := by
        have h13 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        rw [show sin α = -1 by linarith [h10]] at h13
        nlinarith
      have h12 : cos α = 0 := by nlinarith [h11]
      -- This contradicts `h2`
      contradiction
    nlinarith
  have h9 : sin α ^ 2 * (cos α + 1) > 0 := by
    have h10 : sin α ^ 2 > 0 := h5
    have h11 : cos α + 1 > 0 := h7
    nlinarith
  have h10 : cos α ^ 2 * (sin α + 1) > 0 := by
    have h11 : cos α ^ 2 > 0 := h6
    have h12 : sin α + 1 > 0 := h8
    nlinarith
  have h11 : sin α * (cos α + 1) / cos α / (cos α * (sin α + 1) / sin α) = (sin α ^ 2 * (cos α + 1)) / (cos α ^ 2 * (sin α + 1)) := by
    have h12 : sin α ≠ 0 := h1
    have h13 : cos α ≠ 0 := h2
    field_simp [h12, h13]
    all_goals
    nlinarith [Real.sin_sq_add_cos_sq α, sq_pos_of_ne_zero (show sin α ≠ 0 by exact h1), sq_pos_of_ne_zero (show cos α ≠ 0 by exact h2)]
  rw [h11]
  apply div_pos
  · exact h9
  · exact h10