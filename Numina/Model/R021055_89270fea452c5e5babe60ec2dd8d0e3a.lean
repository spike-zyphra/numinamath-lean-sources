import Mathlib

open Real Set
open scoped Real

theorem algebra_303039 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : α + β + γ = π) (f : ℝ → ℝ)
    (hf : f = λ x => (1 + 2 * x - x ^ 2) / ((1 + x) * (1 + x ^ 2))) :
    f (tan α) + f (tan β) + f (tan γ) + f (cot α) + f (cot β) + f (cot γ) = 3 := by
  have h1 : ∀ x > 0, f x + f (1 / x) = 1 := by
    intro x hx
    rw [hf]
    field_simp [hx]
    <;> ring_nf
  have hα1 : tan α > 0 := by 
    have h1 : α > 0 := h₀.1
    have h2 : α < π / 2 := h₀.2
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith
    linarith
  have hβ1 : tan β > 0 := by 
    have h1 : β > 0 := h₁.1
    have h2 : β < π / 2 := h₁.2
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith
    linarith
  have hγ1 : tan γ > 0 := by 
    have h1 : γ > 0 := h₂.1
    have h2 : γ < π / 2 := h₂.2
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith
    linarith
  have hα3 : f (tan α) + f (cot α) = 1 := by
    have h2 : cot α = 1 / (tan α) := by
      field_simp [cot_eq_cos_div_sin, tan_eq_sin_div_cos]
    rw [h2]
    specialize h1 (tan α) hα1
    simpa using h1
  have hβ3 : f (tan β) + f (cot β) = 1 := by
    have h2 : cot β = 1 / (tan β) := by
      field_simp [cot_eq_cos_div_sin, tan_eq_sin_div_cos]
    rw [h2]
    specialize h1 (tan β) hβ1
    simpa using h1
  have hγ3 : f (tan γ) + f (cot γ) = 1 := by
    have h2 : cot γ = 1 / (tan γ) := by
      field_simp [cot_eq_cos_div_sin, tan_eq_sin_div_cos]
    rw [h2]
    specialize h1 (tan γ) hγ1
    simpa using h1
  linarith [hα3, hβ3, hγ3]