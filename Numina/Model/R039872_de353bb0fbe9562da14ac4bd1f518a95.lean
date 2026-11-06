import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246650 (f : ℝ → ℝ) (hf : f = λ x => (x^2 - 2 * x + 1) / (2 * x^2 + 2 * x + 1)) 
    (h1 : ∀ x : ℝ, 2 * x^2 + 2 * x + 1 ≠ 0):
    IsGreatest (range f) (5) ∧ IsLeast (range f) (0) := by
  constructor
  · -- Show that 5 is greatest in range
    constructor
    · -- Show that 5 is in range
      use -2 / 3
      rw [hf]
      norm_num
    · -- Show that 5 is greatest
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h2 : 2 * x^2 + 2 * x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      have h3 : (x ^ 2 - 2 * x + 1) / (2 * x ^ 2 + 2 * x + 1) ≤ 5 := by
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (x + 2 / 3)]
      linarith [h3, hx]
  · -- Show that 0 is least in range
    constructor
    · -- Show that 0 is in range
      use 1
      rw [hf]
      norm_num
    · -- Show that 0 is least
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h2 : 2 * x^2 + 2 * x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      have h3 : 0 ≤ (x^2 - 2 * x + 1) / (2 * x^2 + 2 * x + 1) := by
        apply div_nonneg
        · -- Numerator is (x - 1)^2, which is non-negative
          nlinarith [sq_nonneg (x - 1)]
        · -- Denominator is positive
          linarith [h2]
      linarith [h3, hx]