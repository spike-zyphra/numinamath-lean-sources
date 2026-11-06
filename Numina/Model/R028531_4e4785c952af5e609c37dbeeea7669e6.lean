import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13503 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1/x + 1/(x + 1/x)) :
  IsLeast {y | ∃ x, 0 < x ∧ f x = y} (5/2) := by
  constructor
  · -- Show 5/2 is in the set.
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Calculate f(1) and show it equals 5/2
      rw [h₀]
      norm_num
  · -- Show that 5/2 is a lower bound.
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx_eq_y⟩
    rw [h₀ x] at hfx_eq_y
    have h2 : x + 1 / x ≥ 2 := by
      have h3 : x > 0 := hx_pos
      have h4 : x + 1 / x - 2 ≥ 0 := by
        have h5 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          ring
        rw [h5]
        have h6 : (x - 1) ^ 2 ≥ 0 := by
          exact sq_nonneg (x - 1)
        have h7 : (x - 1) ^ 2 / x ≥ 0 := by
          apply div_nonneg
          exact h6
          linarith
        linarith
      linarith
    have h3 : x + 1 / x ≥ 2 := h2
    have h4 : x + 1 / x + 1 / (x + 1 / x) ≥ 5 / 2 := by
      have h7 : x + 1 / x > 0 := by
        have h1pos : x > 0 := hx_pos
        positivity
      have h8 : x + 1 / x + 1 / (x + 1 / x) - 5 / 2 ≥ 0 := by
        have h7 : x + 1 / x > 0 := by
          positivity
        have h8 : (x + 1 / x + 1 / (x + 1 / x) - 5 / 2) = (2 * (x + 1 / x)^2 + 2 - 5 * (x + 1 / x)) / (2 * (x + 1 / x)) := by
          field_simp
          ring
        rw [h8] at *
        apply div_nonneg
        nlinarith [sq_nonneg (x + 1 / x - 2), sq_nonneg (x - 1), sq_nonneg ((x + 1 / x) - 1 / 2), h2, mul_pos hx_pos (show 0 < x by linarith)]
        nlinarith
      linarith
    have h5 : x + 1 / x + 1 / (x + 1 / x) ≥ 5 / 2 := h4
    linarith