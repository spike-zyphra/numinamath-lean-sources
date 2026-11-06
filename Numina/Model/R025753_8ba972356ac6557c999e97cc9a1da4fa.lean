import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_597709 (x : ℝ) (hx : 0 < x) :
    2 * x + 1 / x ^ 2 ≥ 3 ∧ (∃ x : ℝ, 0 < x ∧ 2 * x + 1 / x ^ 2 = 3) := by
  have h1 : 2 * x + 1 / x ^ 2 ≥ 3 := by
    have hx2_pos : 0 < x ^ 2 := by
      nlinarith
    have h2 : 2 * x ^ 3 + 1 ≥ 3 * x ^ 2 := by
      have h3 : 2 * x ^ 3 + 1 - 3 * x ^ 2 ≥ 0 := by
        have h4 : 2 * x ^ 3 + 1 - 3 * x ^ 2 = 2 * (x - 1) ^ 2 * (x + 1 / 2) := by
          ring
        rw [h4] at *
        have hx5_pos : 0 < x + 1 / 2 := by
          nlinarith
        have h6 : 2 * (x - 1) ^ 2 * (x + 1 / 2) ≥ 0 := by
          positivity
        linarith
      linarith
    have h7 : 2 * x + 1 / x ^ 2 ≥ 3 := by
      have h8 : 2 * x ^ 3 + 1 ≥ 3 * x ^ 2 := h2
      have h9 : (2 * x + 1 / x ^ 2) - 3 ≥ 0 := by
        have h11 : (2 * x + 1 / x ^ 2) - 3 = (2 * x ^ 3 + 1 - 3 * x ^ 2) / x ^ 2 := by
          field_simp
          <;> nlinarith
        rw [h11] at *
        have h12 : 2 * x ^ 3 + 1 - 3 * x ^ 2 ≥ 0 := by linarith
        have h13 : x ^ 2 > 0 := by positivity
        apply div_nonneg
        · linarith
        · nlinarith
      linarith
    exact h7
  constructor
  · exact h1
  · use 1
    constructor
    · norm_num
    · norm_num