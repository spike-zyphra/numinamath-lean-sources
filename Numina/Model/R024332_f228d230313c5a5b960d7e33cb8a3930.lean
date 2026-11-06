import Mathlib

open Real

theorem algebra_93472 (f : ℝ → ℝ)
    (h₀ : ∀ x > 0, f x = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3))) :
    IsLeast {y | ∃ x > 0, f x = y} 6 := by
  constructor
  · -- We need to show 6 is in the set.
    use 1
    constructor
    · norm_num
    · -- Show that f(1) = 6
      norm_num [h₀]
  · -- We need to show 6 is the least element in the set.
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have h1 : f x = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := h₀ x hx
    rw [h1] at hfx
    have h2 : ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) = 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h2] at hfx
    have h4 : x + 1 / x ≥ 2 := by
      have h5 : x > 0 := hx
      have h6 : x + 1 / x - 2 ≥ 0 := by
        have h7 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          ring
        rw [h7] at *
        apply div_nonneg
        · -- Show (x - 1)^2 ≥ 0
          apply pow_two_nonneg
        · -- Show x > 0
          linarith
      linarith
    have h7 : 3 * (x + 1 / x) ≥ 6 := by
      linarith [h4]
    linarith [h7, hfx]