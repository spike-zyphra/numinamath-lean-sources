import Mathlib

open Real Set
open scoped Real

theorem algebra_634415 {α : ℝ} (ha : ¬ ∃ k : ℤ, α = k * π / 2) :
    (sin α + tan α) / (cos α + 1 / tan α) > 0 := by
  have h1 : sin α ≠ 0 := by 
    by_contra h 
    have : ∃ k : ℤ, α = k * π / 2 := by 
      have h3 : sin α = 0 := h 
      obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h3 
      refine ⟨2 * k, by 
        field_simp [show π ≠ 0 by linarith [Real.pi_pos]] at *
        <;> ring_nf at *
        <;> linarith [hk]
      ⟩ 
    contradiction 
  have h2 : cos α ≠ 0 := by 
    by_contra h 
    have : ∃ k : ℤ, α = k * π / 2 := by 
      have h3 : cos α = 0 := h 
      obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 h3 
      refine ⟨2 * k + 1, by 
        field_simp [show π ≠ 0 by linarith [Real.pi_pos]] at *
        <;> ring_nf at *
        <;> linarith [hk]
      ⟩ 
    contradiction 
  have htan : tan α = sin α / cos α := by 
    rw [tan_eq_sin_div_cos] 
  have htan2 : 1 / tan α = cos α / sin α := by 
    rw [htan] 
    field_simp [h1, h2] 
  have h3 : sin α + tan α = sin α * (cos α + 1) / cos α := by 
    rw [htan] 
    field_simp [h2] 
    <;> ring 
  have h4 : cos α + 1 / tan α = cos α * (sin α + 1) / sin α := by 
    rw [htan2] 
    field_simp [h1, h2] 
    <;> ring 
  rw [h3, h4] 
  have h5 : (sin α * (cos α + 1) / cos α) / (cos α * (sin α + 1) / sin α) = (sin α ^ 2 * (cos α + 1)) / (cos α ^ 2 * (sin α + 1)) := by 
    field_simp [h1, h2]
    <;> ring 
  rw [h5] 
  have h6 : sin α ^ 2 > 0 := by 
    have h1' : sin α ≠ 0 := h1 
    have h7 : sin α ^ 2 > 0 := by 
      exact sq_pos_of_ne_zero h1' 
    linarith 
  have h7 : cos α ^ 2 > 0 := by 
    have h2' : cos α ≠ 0 := h2 
    have h8 : cos α ^ 2 > 0 := by 
      exact sq_pos_of_ne_zero h2' 
    linarith 
  -- Show that cos α + 1 > 0 and sin α + 1 > 0
  have h8 : cos α + 1 > 0 := by 
    nlinarith [sq_pos_of_ne_zero (show sin α ≠ 0 by exact h1), sq_pos_of_ne_zero (show cos α ≠ 0 by exact h2), Real.sin_sq_add_cos_sq α, sq_nonneg (sin α), sq_nonneg (cos α + 1)]
  have h9 : sin α + 1 > 0 := by 
    nlinarith [sq_pos_of_ne_zero (show sin α ≠ 0 by exact h1), sq_pos_of_ne_zero (show cos α ≠ 0 by exact h2), Real.sin_sq_add_cos_sq α, sq_nonneg (cos α), sq_nonneg (sin α + 1)]
  have h10 : cos α ^ 2 * (sin α + 1) > 0 := by 
    have h11 : cos α ^ 2 > 0 := h7 
    have h12 : sin α + 1 > 0 := h9 
    nlinarith 
  apply div_pos 
  · -- Show the numerator is positive 
    have h11 : sin α ^ 2 * (cos α + 1) > 0 := by 
      have h12 : sin α ^ 2 > 0 := h6 
      have h13 : cos α + 1 > 0 := h8 
      nlinarith 
    linarith 
  · -- Show the denominator is positive 
    linarith