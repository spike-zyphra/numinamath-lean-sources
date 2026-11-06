import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315458 (f : ℝ → ℝ) (hf : f = λ x => (x + 1)^3 * (x^3 + 5 * x)) :
    {x | f x < 10 * (x + 1)^2 + 8} = {x | -2 < x ∧ x < 1} := by
  -- We use extensionality to prove equality of sets by showing membership equivalence
  ext x
  -- Simplify the goal using the definition of f
  simp [hf]
  -- Split the proof into two directions: forward and backward implications
  constructor
  -- Forward direction: if f(x) < 10(x+1)^2 + 8, then -2 < x < 1
  ·
    intro h
    -- Rearrange the inequality to standard form
    have h1 : (x + 1) ^ 3 * (x^3 + 5 * x) - (10 * (x + 1) ^ 2 + 8) < 0 := by linarith
    -- Factor the expression into a product of terms
    have h2 : (x - 1) * (x + 2) * (x^4 + 2 * x^3 + 8 * x^2 + 12 * x + 9) < 0 := by
      ring_nf at h1 ⊢
      nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x + 6 / 7), sq_nonneg (x ^ 2 + x + 3 / 14)]
    -- Prove that the polynomial factor is always positive
    have h3 : x^4 + 2 * x^3 + 8 * x^2 + 12 * x + 9 > 0 := by
      nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x + 6 / 7), sq_nonneg (x ^ 2 + x + 3 / 14)]
    -- Deduce that (x-1)(x+2) < 0
    have h4 : (x - 1) * (x + 2) < 0 := by nlinarith [h2, h3]
    -- Now prove both bounds: -2 < x and x < 1
    constructor
    -- Prove -2 < x by contradiction
    ·
      by_contra h5
      push_neg at h5
      nlinarith [h4, sq_nonneg (x - 1), sq_nonneg (x + 2)]
    -- Prove x < 1 by contradiction
    ·
      by_contra h6
      push_neg at h6
      nlinarith [h4, sq_nonneg (x - 1), sq_nonneg (x + 2)]
  -- Backward direction: if -2 < x < 1, then f(x) < 10(x+1)^2 + 8
  ·
    rintro ⟨h1, h2⟩
    -- Show that (x-1)(x+2) < 0 when -2 < x < 1
    have h3 : (x - 1) * (x + 2) < 0 := by
      apply mul_neg_of_neg_of_pos
      · linarith
      · linarith
    -- Show that the polynomial factor is positive
    have h4 : x^4 + 2 * x^3 + 8 * x^2 + 12 * x + 9 > 0 := by
      nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x + 6 / 7), sq_nonneg (x ^ 2 + x + 3 / 14)]
    -- Deduce that the product is negative
    have h5 : (x - 1) * (x + 2) * (x^4 + 2 * x^3 + 8 * x^2 + 12 * x + 9) < 0 := by
      apply mul_neg_of_neg_of_pos
      · exact h3
      · nlinarith
    -- Complete the proof using linear arithmetic
    linarith
