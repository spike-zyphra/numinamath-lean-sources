import Mathlib

open Real Set
open scoped Real

theorem algebra_306131 {x : ℝ} (hx : x = 5 * π / 4) :
    tan x = 1 ∧ ¬ (∀ y, tan y = 1 → y = x) := by
  have h1 : tan x = 1 := by
    rw [hx]
    have : 5 * π / 4 = π / 4 + π := by
      linarith [Real.pi_pos]
    rw [this]
    have h2 : tan (π / 4 + π) = 1 := by
      have h3 : tan (π / 4 + π) = tan (π / 4) := by
        rw [tan_add_pi]
      rw [h3]
      have h4 : tan (π / 4) = 1 := by
        rw [tan_eq_sin_div_cos]
        have h1 : sin (π / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
        have h2 : cos (π / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
        rw [h1, h2]
        field_simp
      exact h4
    exact h2
  have h2 : ¬ (∀ y, tan y = 1 → y = x) := by
    intro h
    have h3 := h (Real.pi / 4)
    have htan1 : tan (Real.pi / 4) = 1 := by
      rw [tan_eq_sin_div_cos]
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
      rw [h1, h2]
      field_simp
    have heq : Real.pi / 4 = x := by
      apply h3
      exact htan1
    rw [hx] at heq
    nlinarith [Real.pi_pos]
  exact ⟨h1, h2⟩