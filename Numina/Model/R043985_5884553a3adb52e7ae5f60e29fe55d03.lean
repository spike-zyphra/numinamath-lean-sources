import Mathlib

theorem inequalities_292471 (x : ℝ) (hx : 0 < x) :
    x^3 + 1 / x ≥ 2 * x ∧ (x = 1 ↔ x^3 + 1 / x = 2 * x) := by
  have h1 : x^3 + 1 / x ≥ 2 * x := by
    have h2 : x > 0 := hx
    have h4 : x ^ 3 + 1 / x - 2 * x ≥ 0 := by
      have h5 : x ^ 3 + 1 / x - 2 * x = (x ^ 4 + 1 - 2 * x^2) / x := by
        field_simp
        <;> ring
      rw [h5]
      have h6 : x ^ 4 + 1 - 2 * x^2 ≥ 0 := by
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1)]
      have h7 : (x ^ 4 + 1 - 2 * x^2) / x ≥ 0 := by
        apply div_nonneg
        · linarith
        all_goals positivity
      linarith
    linarith
  constructor
  · exact h1
  · -- Now to prove the equality case
    constructor
    · -- (→) direction: assume x = 1, prove x^3 + 1/x = 2x
      intro h_eq
      rw [h_eq]
      norm_num
    · -- (←) direction: assume x^3 + 1/x = 2x, prove x = 1
      intro h_eq
      have h2 : x > 0 := hx
      have h3 : x^3 + 1 / x = 2 * x := h_eq
      have h4 : x ^ 4 + 1 - 2 * x^2 = 0 := by
        have h5 : x ^ 3 + 1 / x = 2 * x := h_eq
        have h6 : (x ^ 3 + 1 / x) * x = (2 * x) * x := by
          rw [h5]
        have h7 : (x ^ 3 + 1 / x) * x = x ^ 4 + 1 := by
          field_simp
          <;> nlinarith
        have h8 : (2 * x) * x = 2 * x^2 := by
          ring
        have h9 : x ^ 4 + 1 = 2 * x^2 := by
          nlinarith [h7, h8, h6]
        linarith
      have h8 : (x ^ 2 - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), h4]
      have h9 : x ^ 2 - 1 = 0 := by
        nlinarith [h8]
      have h10 : x ^ 2 = 1 := by
        nlinarith
      have h11 : x = 1 := by
        nlinarith [h10, sq_nonneg (x - 1)]
      linarith