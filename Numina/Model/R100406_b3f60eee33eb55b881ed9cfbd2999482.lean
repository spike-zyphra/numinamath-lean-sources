import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_222778 (f : ℝ → ℝ) (hf : f = λ x => (1 + x + x^2) / (1 - x + x^2)) :
    IsLeast (range f) (1 / 3) ∧ IsGreatest (range f) 3 := by
  constructor
  · -- Show that 1/3 is in the range of f
    constructor
    · -- Show that 1/3 is attained
      use -1
      simp [hf]
      norm_num
    · -- Show that 1/3 is a lower bound
      intro y hy
      rcases hy with ⟨x, hx⟩
      simp [hf] at hx
      have h1 : 0 < 1 - x + x^2 := by 
        nlinarith [sq_nonneg (x - 1 / 2)]
      have h2 : (1 + x + x^2) ≥ (1 / 3) * (1 - x + x^2) := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      have h3 : (1 + x + x^2) / (1 - x + x^2) ≥ (1 / 3) := by
        apply (le_div_iff₀ h1).mpr
        linarith [h2]
      linarith [hx, h3]
  · -- Show that 3 is in the range of f
    constructor
    · -- Show that 3 is attained
      use 1
      simp [hf]
      norm_num
    · -- Show that 3 is an upper bound
      intro y hy
      rcases hy with ⟨x, hx⟩
      simp [hf] at hx
      have h1 : 0 < 1 - x + x^2 := by 
        nlinarith [sq_nonneg (x - 1 / 2)]
      have h2 : (1 + x + x^2) ≤ 3 * (1 - x + x^2) := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h3 : (1 + x + x^2) / (1 - x + x^2) ≤ 3 := by
        apply (div_le_iff₀ h1).mpr
        linarith [h2]
      linarith [hx, h3]