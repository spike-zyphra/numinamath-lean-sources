import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_284941 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (2 * x ^ 2 + 6 * x + 6) / (x ^ 2 + 4 * x + 5)) :
  IsGreatest (range f) 3 ∧ IsLeast (range f) 1 := by
  constructor
  · -- Prove 3 is greatest
    constructor
    · -- Show 3 is in range f
      use -3
      rw [h₀]
      norm_num
    · -- Show no value greater than 3 is in range
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [h₀] at hx
      have h1 : (2 * x ^ 2 + 6 * x + 6) / (x ^ 2 + 4 * x + 5) ≤ 3 := by
        have hx2 : x^2 + 4 * x + 5 > 0 := by 
          nlinarith [sq_nonneg (x + 2)]
        apply (div_le_iff (by linarith)).mpr
        nlinarith [sq_nonneg (x + 3)]
      linarith [h1, hx]
  · -- Prove 1 is least
    constructor
    · -- Show 1 is in range f
      use -1
      rw [h₀]
      norm_num
    · -- Show no value less than 1 is in range
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [h₀] at hx
      have h2 : (2 * x ^ 2 + 6 * x + 6) / (x ^ 2 + 4 * x + 5) ≥ 1 := by
        have hx2 : x^2 + 4 * x + 5 > 0 := by 
          nlinarith [sq_nonneg (x + 2)]
        apply (le_div_iff (by linarith)).mpr
        nlinarith [sq_nonneg (x + 1)]
      linarith [h2, hx]