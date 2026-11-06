import Mathlib

theorem algebra_189957 (x : ℝ) :
    x^6 - 9 * x^3 + 8 > 0 ↔ x < 1 ∨ x > 2 := by

  constructor
  · -- Assume x^6 - 9 * x^3 + 8 > 0, prove x < 1 ∨ x > 2
    intro h
    have h1 : (x^3 - 1) * (x^3 - 8) > 0 := by
      nlinarith [sq_nonneg (x^3 - 1), sq_nonneg (x^3 - 8), sq_nonneg (x^3 - 4), sq_nonneg (x^3 * (x^3 - 8)), sq_nonneg (x ^ 3 * 1)]

    cases (mul_pos_iff.mp h1) with
    | inl h2 =>
      -- This is the case where both factors in the product are positive.
      -- That is, (x^3 - 1) > 0 and (x^3 - 8) > 0.
      -- From (x^3 - 8) > 0, we have x^3 > 8, which implies x > 2.
      have h3 : x^3 - 8 > 0 := by linarith [h2.2]
      have h4 : x ^ 3 > 8 := by linarith
      have h5 : x > 2 := by
        by_contra h6
        push_neg at h6
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x^2 - 4), sq_nonneg (x ^ 2 * (x - 2)), sq_nonneg (x ^ 3 - 8)]
      right
      exact h5
    | inr h2 =>
      -- This is the case where both factors in the product are negative.
      -- That is, (x^3 - 1) < 0 and (x^3 - 8) < 0.
      -- From (x^3 - 1) < 0, we have x^3 < 1, which implies x < 1.
      have h3 : x^3 - 1 < 0 := by linarith [h2.1]
      have h4 : x ^ 3 < 1 := by linarith
      have h5 : x < 1 := by
        by_contra h6
        push_neg at h6
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x ^ 2 * (x - 1)), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 * (x - 1))]
      left
      exact h5
  · -- Assume x < 1 ∨ x > 2, prove x^6 - 9 * x^3 + 8 > 0
    intro h
    cases h with
    | inl h1 =>
      -- Case where x < 1.
      -- From x < 1, we have x^3 < 1, so x^3 - 1 < 0.
      -- From x < 2, we have x^3 < 8, so x^3 - 8 < 0.
      -- The product of two negatives is positive, so (x^3 - 1)(x^3 - 8) > 0.
      have h2 : x^3 < 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x ^ 2 * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x^3 - 1), sq_nonneg (x - 0)]
      have h3 : x^3 < 8 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x^2 - 4), sq_nonneg (x ^ 2 * (x - 2)), sq_nonneg ((x + 2) * (x - 2)), sq_nonneg (x^3 - 8)]
      -- Show that (x^3 - 1) * (x^3 - 8) > 0.
      have h4 : (x^3 - 1) * (x^3 - 8) > 0 := by
        nlinarith
      nlinarith [sq_nonneg (x^3 - 1), sq_nonneg (x^3 - 8), sq_nonneg (x^3 * (x^3 - 8)), sq_nonneg (x ^ 3 * (x^3 - 1)), sq_nonneg ((x^3) ^ 2 * (x^3)), sq_nonneg (x^3 * (x^3)), sq_nonneg ((x ^ 3 - 1) * (x ^ 3 - 8)), sq_nonneg (x ^ 3 * (x ^ 3 - 8))]
    | inr h2 =>
      -- Case where x > 2.
      -- From x > 2, we have x^3 > 8, so x^3 - 8 > 0.
      -- From x > 2, we also have x^3 > 1, so x^3 - 1 > 0.
      -- The product of two positives is positive, so (x^3 - 1)(x^3 - 8) > 0.
      have h3 : x^3 > 8 := by
        have h4 : x > 2 := h2
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x^2 - 4), sq_nonneg (x ^ 2 * (x - 2)), sq_nonneg ((x + 2) * (x - 2)), sq_nonneg (x^3 - 8)]
      have h4 : x^3 > 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x ^ 2 * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x^3 - 1), sq_nonneg (x ^ 2 * (x - 0))]
      -- Show that (x^3 - 1) * (x^3 - 8) > 0.
      have h5 : (x^3 - 1) * (x^3 - 8) > 0 := by
        nlinarith
      nlinarith [sq_nonneg (x^3 - 1), sq_nonneg (x^3 - 8), sq_nonneg (x^3 * (x^3 - 8)), sq_nonneg (x ^ 3 * (x^3 - 1)), sq_nonneg ((x^3) ^ 2 * (x^3)), sq_nonneg (x^3 * (x^3)), sq_nonneg ((x ^ 3 - 1) * (x ^ 3 - 8)), sq_nonneg (x ^ 3 * (x ^ 3 - 8))]