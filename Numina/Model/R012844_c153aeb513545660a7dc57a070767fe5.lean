import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_186826 (α β : ℝ) (hβ : β ≠ 0) :
  ∀ a b : ℝ, (∀ x : ℝ, a * exp (α * x) * sin (β * x) + b * exp (α * x) * cos (β * x) = 0) ↔
  a = 0 ∧ b = 0 := by
  intro a b
  constructor
  · -- Assume that ∀ x : ℝ, a * exp (α * x) * sin (β * x) + b * exp (α * x) * cos (β * x) = 0, prove a = 0 ∧ b = 0
    intro h
    have eq1 := h 0
    have hb : b = 0 := by 
      simp [exp_zero] at eq1 
      linarith
    have eq2 := h (Real.pi / (2 * β))
    have h1 : β * (Real.pi / (2 * β)) = Real.pi / 2 := by
      field_simp [hβ]
      <;> ring
    have eq3 : sin (β * (Real.pi / (2 * β))) = 1 := by
      rw [h1]
      exact sin_pi_div_two
    have eq4 : cos (β * (Real.pi / (2 * β))) = 0 := by
      rw [h1]
      have : cos (Real.pi / 2) = 0 := by
        exact cos_pi_div_two
      linarith
    have eq5 : a * exp (α * (Real.pi / (2 * β))) * sin (β * (Real.pi / (2 * β))) + b * exp (α * (Real.pi / (2 * β))) * cos (β * (Real.pi / (2 * β))) = 0 := eq2
    rw [eq3, eq4, hb] at eq5
    have h2 : exp (α * (Real.pi / (2 * β))) ≠ 0 := exp_ne_zero (α * (Real.pi / (2 * β)))
    have ha : a = 0 := by
      apply (mul_left_inj' h2).mp 
      linarith 
    exact ⟨ha, hb⟩
  · -- Assume a = 0 ∧ b = 0, prove ∀ x : ℝ, a * exp (α * x) * sin (β * x) + b * exp (α * x) * cos (β * x) = 0
    rintro ⟨rfl, rfl⟩ 
    intro x 
    simp