import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146997 (f : ℝ → ℝ) (hf : f = λ x => (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1)) :
    IsLeast (range f) (-4) ∧ IsGreatest (range f) 1 := by
  have h1 : ∀ x, f x = (x ^ 2 - 2 * x - 3) / (2 * x ^ 2 + 2 * x + 1) := by
    intro x
    rw [hf]
  constructor
  · -- Show that -4 is the least element in the range of f
    constructor
    · -- First, show that -4 is in the range of f
      use -1 / 3
      rw [h1]
      norm_num
    · -- Now, we must prove that -4 is indeed the least element
      intro y
      rintro ⟨x, hx⟩
      rw [h1] at hx
      have h2 : 2 * x ^ 2 + 2 * x + 1 > 0 := by
        nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
      have h3 : (x ^ 2 - 2 * x - 3) / (2 * x ^ 2 + 2 * x + 1) ≥ -4 := by
        have h4 : 2 * x ^ 2 + 2 * x + 1 > 0 := h2
        apply (le_div_iff₀ h4).mpr
        nlinarith [sq_nonneg (x * 3 + 1)]
      linarith
  · -- Show that 1 is the greatest element in the range of f
    constructor
    · -- First, show that 1 is in the range of f
      use -2
      rw [h1]
      norm_num
    · -- Now, we must prove that 1 is indeed the greatest element
      intro y
      rintro ⟨x, hx⟩
      rw [h1] at hx
      have h2 : 2 * x ^ 2 + 2 * x + 1 > 0 := by
        nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
      have h3 : (x ^ 2 - 2 * x - 3) / (2 * x ^ 2 + 2 * x + 1) ≤ 1 := by
        have h4 : 2 * x ^ 2 + 2 * x + 1 > 0 := h2
        apply (div_le_iff₀ h4).mpr
        nlinarith [sq_nonneg (x + 2)]
      linarith