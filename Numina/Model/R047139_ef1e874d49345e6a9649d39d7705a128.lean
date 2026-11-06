import Mathlib

open Real Set
open scoped Real

theorem inequalities_275541 (α β γ : ℝ) 
    (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) :
    6 ≤ tan α * (cot β + cot γ) + tan β * (cot γ + cot α) + tan γ * (cot α + cot β) := by
  rcases h₀ with ⟨hα1, hα2⟩ 
  rcases h₁ with ⟨hβ1, hβ2⟩ 
  rcases h₂ with ⟨hγ1, hγ2⟩ 
  have h1 : 0 < tan α := by 
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]
  have h2 : 0 < tan β := by 
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]
  have h3 : 0 < tan γ := by 
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith [hγ1, hγ2, Real.pi_pos]
    linarith [hγ1, hγ2, Real.pi_pos] 
  have h4 : tan α * (cot β + cot γ) + tan β * (cot γ + cot α) + tan γ * (cot α + cot β) =
      tan α / tan β + tan α / tan γ + tan β / tan γ + tan β / tan α + tan γ / tan α + tan γ / tan β := by
    simp [cot_eq_cos_div_sin, tan_eq_sin_div_cos]
    field_simp [show tan α ≠ 0 by linarith, show tan β ≠ 0 by linarith, show tan γ ≠ 0 by linarith]
    <;> ring
  rw [h4]
  have h5 : tan α / tan β + tan β / tan α ≥ 2 := by
    have h6 : tan α > 0 := h1
    have h7 : tan β > 0 := h2
    have h10 : tan α / tan β + tan β / tan α - 2 ≥ 0 := by
      have h2 : tan α / tan β + tan β / tan α - 2 = (tan α - tan β) ^ 2 / (tan α * tan β) := by
        field_simp
        ring
      rw [h2]
      have h3 : (tan α - tan β) ^ 2 ≥ 0 := by nlinarith
      have h4 : tan α * tan β > 0 := mul_pos h6 h7
      exact div_nonneg h3 (by positivity)
    linarith
  have h8 : tan β / tan γ + tan γ / tan β ≥ 2 := by
    have h7 : tan β > 0 := h2
    have h6 : tan γ > 0 := h3
    have h10 : tan β / tan γ + tan γ / tan β - 2 ≥ 0 := by
      have h2 : tan β / tan γ + tan γ / tan β - 2 = (tan β - tan γ) ^ 2 / (tan β * tan γ) := by
        field_simp
        ring
      rw [h2]
      have h3 : (tan β - tan γ) ^ 2 ≥ 0 := by nlinarith
      have h4 : tan β * tan γ > 0 := mul_pos h7 h6
      exact div_nonneg h3 (by positivity)
    linarith 
  have h9 : tan γ / tan α + tan α / tan γ ≥ 2 := by
    have h6 : tan α > 0 := h1
    have h7 : tan γ > 0 := h3
    have h10 : tan γ / tan α + tan α / tan γ - 2 ≥ 0 := by
      have h2 : tan γ / tan α + tan α / tan γ - 2 = (tan γ - tan α) ^ 2 / (tan γ * tan α) := by
        field_simp
        ring
      rw [h2]
      have h3 : (tan γ - tan α) ^ 2 ≥ 0 := by nlinarith
      have h4 : tan γ * tan α > 0 := mul_pos h7 h6
      exact div_nonneg h3 (by positivity)
    linarith 
  have h6 : tan α / tan β + tan β / tan α + tan β / tan γ + tan γ / tan β + tan γ / tan α + tan α / tan γ ≥ 6 := by
    linarith [h5, h8, h9]
  linarith [h6]