import Mathlib

theorem algebra_202885 (a b : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : b ≠ 0)
    (h₂ : ∃ x y, a * x + b * y = 2 ∧ x^2 / 6 + y^2 / 2 = 1) :
    a / b ≤ -1 ∨ a / b ≥ 1 := by
  rcases h₂ with ⟨x, y, h₃, h₄⟩
  have h5 : x^2 + 3 * y^2 = 6 := by
    linarith [h₄]
  have h6 : (a * x + b * y) ^ 2 ≤ (x^2 + 3 * y^2) * (a^2 + b^2 / 3) := by
    nlinarith [sq_nonneg (x * b - 3 * a * y)]
  have h7 : 3 * a ^ 2 + b ^ 2 ≥ 2 := by
    nlinarith [h₃, h5, h6]
  by_cases h : a / b ≤ -1
  · -- If a/b ≤ -1, then we have the left side of the disjunction.
    left
    assumption
  · -- Now we need to show that a/b ≥ 1
    by_cases h' : a / b ≥ 1
    · -- If a/b ≥ 1, then we have the right side of the disjunction.
      right
      assumption
    · -- Assume that -1 < a/b < 1, derive a contradiction
      have h8 : a / b > -1 := by
        linarith [h]
      have h9 : a / b < 1 := by
        linarith [h']
      have h10 : a ^ 2 < b ^ 2 := by
        by_cases hb1 : b > 0
        · -- If b > 0, then from h8: a/b > -1 means a > -b, and from h9: a/b < 1 means a < b.
          have h11 : -b < a := by
            have : a / b > -1 := h8
            apply (lt_div_iff' (by linarith)).mp at this
            nlinarith
          have h12 : a < b := by
            have : a / b < 1 := h9
            apply (div_lt_iff' (by linarith)).mp at this
            nlinarith
          nlinarith [sq_pos_of_pos hb1, sq_nonneg (a - b)]
        · -- If b ≤ 0, then since b ≠ 0, we have b < 0
          have hb2 : b < 0 := by 
            by_contra h
            push_neg at h
            have h13 : b = 0 := by linarith
            contradiction
          have h11 : a < -b := by
            have : a / b > -1 := h8
            apply (lt_div_iff_of_neg' (by linarith)).mp at this
            nlinarith
          have h12 : -b < a := by
            have : a / b < 1 := h9
            apply (div_lt_iff_of_neg' (by linarith)).mp at this
            nlinarith
          nlinarith [sq_pos_of_neg hb2, sq_nonneg (a + b)]
      have h11 : a^2 + b^2 = 1 := h₀
      have h12 : a^2 < 1 / 2 := by
        nlinarith [h10, h11]
      nlinarith [h7, h12, h₀]