import Mathlib

open Real Set
open scoped Real

theorem algebra_130052 (α : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x ∈ Ioo 0 (π/4), f x = (sin (x + α) + sin (x - α) - 4 * sin x) / (cos (x + α) + cos (x - α) - 4 * cos x)) :
  ∀ x ∈ Ioo 0 (π/4), 0 < f x ∧ f x < 1 := by
  intro x hx
  have h1 : 0 < x := hx.1
  have h2 : x < π / 4 := hx.2
  have hfx : f x = (sin (x + α) + sin (x - α) - 4 * sin x) / (cos (x + α) + cos (x - α) - 4 * cos x) := h₀ x hx
  have hsin1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, Real.pi_pos]
    linarith [h2, Real.pi_pos]
  have hcos1 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h1, Real.pi_pos]
    linarith [h2, Real.pi_pos]
  have hsin_lt_cos : sin x < cos x := by
    have h4 : x < π / 2 - x := by
      nlinarith [h1, h2, Real.pi_pos]
    have h6 : sin x < sin (π / 2 - x) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [h1, h2, Real.pi_pos]
    have h7 : sin (π / 2 - x) = cos x := by
      rw [sin_pi_div_two_sub]
    linarith [h6, h7]
  have h8 : sin (x + α) = sin x * cos α + cos x * sin α := by
    rw [sin_add]
  have h9 : sin (x - α) = sin x * cos α - cos x * sin α := by
    rw [sin_sub]
  have h10 : cos (x + α) = cos x * cos α - sin x * sin α := by
    rw [cos_add]
  have h11 : cos (x - α) = cos x * cos α + sin x * sin α := by
    rw [cos_sub]
  have h12 : sin (x + α) + sin (x - α) = 2 * sin x * cos α := by
    rw [h8, h9]
    ring
  have h13 : cos (x + α) + cos (x - α) = 2 * cos x * cos α := by
    rw [h10, h11]
    ring
  rw [hfx]
  have h20 : sin (x + α) + sin (x - α) - 4 * sin x = 2 * sin x * cos α - 4 * sin x := by
    linarith [h12]
  have h21 : cos (x + α) + cos (x - α) - 4 * cos x = 2 * cos x * cos α - 4 * cos x := by
    linarith [h13]
  rw [h20, h21]
  have h40 : cos α ≠ 2 := by
    have h41 : cos α ≤ 1 := by
      apply cos_le_one
    have h42 : cos α ≥ -1 := by
      linarith [neg_one_le_cos α, cos_le_one α]
    by_contra h
    have h43 : cos α > 1 := by
      linarith [h, h42]
    have h44 : cos α ≤ 1 := by
      apply cos_le_one
    linarith
  have h45 : 2 * sin x * cos α - 4 * sin x = 2 * sin x * (cos α - 2) := by ring
  have h46 : 2 * cos x * cos α - 4 * cos x = 2 * cos x * (cos α - 2) := by ring
  rw [h45, h46]
  have hcosne : cos α - 2 ≠ 0 := by
    intro h0
    have hne : cos α = 2 := by linarith
    contradiction
  have htan : (2 * sin x * (cos α - 2)) / (2 * cos x * (cos α - 2)) = sin x / cos x := by
    have h1 : cos α - 2 ≠ 0 := hcosne
    have h2 : 2 * cos x * (cos α - 2) ≠ 0 := by
      have hcosxne : cos x ≠ 0 := by
        linarith [hcos1]
      by_contra h
      have : cos x = 0 ∨ cos α - 2 = 0 := by
        cases (mul_eq_zero.mp h) with
        | inl h1 => 
          have : cos x = 0 := by linarith
          tauto
        | inr h2 => 
          tauto
      cases this with
      | inl h0 =>
        tauto
      | inr h0 =>
        contradiction
    have hcosxne : cos x ≠ 0 := by
      linarith [hcos1]
    field_simp [h2, hcosxne, h1]
    <;> ring
  rw [htan]
  constructor
  · -- Show that $0 < \sin x / \cos x$
    apply div_pos
    all_goals linarith [hsin1, hcos1]
  · -- Show that $\sin x / \cos x < 1$
    have h : sin x < cos x := hsin_lt_cos
    have hcos1 : cos x > 0 := hcos1
    apply (div_lt_iff₀ hcos1).mpr
    linarith