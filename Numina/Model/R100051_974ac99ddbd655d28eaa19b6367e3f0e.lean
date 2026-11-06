import Mathlib

theorem algebra_287540 (x : ℝ) : x^4 - 3 * x^3 + x^2 - 3 * x = 0 ↔ x = 0 ∨ x = 3 := by
  constructor
  · -- Assume x^4 - 3 * x^3 + x^2 - 3 * x = 0, prove x = 0 ∨ x = 3
    intro h
    -- Factor the polynomial as x(x^3 - 3x^2 + x - 3)
    have h1 : x * (x ^ 3 - 3 * x ^ 2 + x - 3) = 0 := by
      ring_nf at h ⊢
      linarith
    -- Use the zero product property
    cases' (mul_eq_zero.mp h1) with hx hx
    · -- Case where x = 0
      left
      exact hx
    · -- Case where x^3 - 3x^2 + x - 3 = 0
      have h2 : (x ^ 3 - 3 * x ^ 2 + x - 3) = (x - 3) * (x ^ 2 + 1) := by
        ring_nf
      have h3 : (x - 3) * (x ^ 2 + 1) = 0 := by
        rw [h2] at hx
        linarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- Case where x - 3 = 0, so x = 3
        right
        linarith
      · -- Case where x^2 + 1 = 0
        exfalso
        have h6 : x ^ 2 = -1 := by
          linarith
        have h7 : x ^ 2 ≥ 0 := by
          apply sq_nonneg
        -- Contradiction since x^2 = -1 < 0
        linarith
  · -- Assume x = 0 ∨ x = 3, prove x^4 - 3 * x^3 + x^2 - 3 * x = 0
    rintro (h | h)
    · -- Case where x = 0
      rw [h]
      all_goals norm_num
    · -- Case where x = 3
      rw [h]
      all_goals norm_num