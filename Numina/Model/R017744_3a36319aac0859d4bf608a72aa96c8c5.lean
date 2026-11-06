import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_170716 (x : ℝ) :
  x^2 ≠ 0 ∧ (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0 ↔
  x ∈ Ioo (-2) 0 ∪ Ioo 0 1 := by
  constructor
  · -- Assume x^2 ≠ 0 ∧ (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0, prove x ∈ Ioo (-2) 0 ∪ Ioo 0 1
    intro h
    rcases h with ⟨hx1, hx2⟩
    have hx3 : x ≠ 0 := by
      intro h'
      have : x ^ 2 = 0 := by
        rw [h']
        norm_num
      contradiction
    have h1 : x ^ 4 + 3 * x ^ 3 + 4 * x ^ 2 - 8 < 0 := by
      have h2 : x^2 > 0 := by
        have : x ≠ 0 := hx3
        exact sq_pos_of_ne_zero this
      have h3 : (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0 := hx2
      apply (div_neg_iff).mp at h3
      cases h3 with
      | inl h4 =>
        have : x ^ 4 + 3 * x ^ 3 + 4 * x ^ 2 - 8 < 0 := by
          linarith
        linarith
      | inr h4 =>
        nlinarith [sq_nonneg x]
    have h2_pos : x^2 + 2 * x + 4 > 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 2)]
    have h3 : (x - 1) * (x + 2) < 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2)]
    have h4 : x > -2 := by
      nlinarith
    have h5 : x < 1 := by
      nlinarith
    by_cases h6 : x < 0
    · -- Show x ∈ Ioo (-2) 0
      have h7 : x ∈ Ioo (-2) 0 := ⟨by linarith, by linarith⟩
      left
      exact h7
    · -- Show x ∈ Ioo 0 1
      have h7 : x > 0 := by
        by_contra h
        push_neg at h
        have : x = 0 := by
          nlinarith
        contradiction
      have h8 : x ∈ Ioo 0 1 := ⟨by linarith, by linarith⟩
      right
      exact h8
  · -- Show x^2 ≠ 0 ∧ (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0
    rintro (h | h)
    · -- Case x ∈ (-2, 0)
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- Show x^2 ≠ 0
        intro h'
        have : x = 0 := by
          nlinarith
        linarith
      · -- Show (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0
        have h3 : x < 0 := by linarith
        have h2_pos : (x - 1) * (x + 2) < 0 := by
          nlinarith
        have h2_pos2 : x ^ 2 + 2 * x + 4 > 0 := by
          nlinarith [sq_nonneg (x + 1)]
        have h1 : x ^ 4 + 3 * x ^ 3 + 4 * x ^ 2 - 8 < 0 := by
          have h2_pos3 : (x - 1) * (x + 2) * (x ^ 2 + 2 * x + 4) < 0 := by 
            nlinarith [h2_pos, h2_pos2, sq_nonneg (x - 1), sq_nonneg (x + 2)]
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1)]
        have h2 : x^2 > 0 := by
          have hx3 : x ≠ 0 := by linarith
          exact sq_pos_of_ne_zero hx3
        apply div_neg_of_neg_of_pos
        · -- Show x^4 + 3 * x^3 + 4 * x^2 - 8 < 0
          linarith
        · -- Show x^2 > 0
          exact h2
    · -- Case x ∈ (0, 1)
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- Show x^2 ≠ 0
        intro h'
        have : x = 0 := by
          nlinarith
        linarith
      · -- Show (x^4 + 3 * x^3 + 4 * x^2 - 8) / x^2 < 0
        have h3 : x > 0 := by linarith
        have h2_pos : (x - 1) * (x + 2) < 0 := by
          nlinarith
        have h2_pos2 : x ^ 2 + 2 * x + 4 > 0 := by
          nlinarith [sq_nonneg (x + 1)]
        have h1 : x ^ 4 + 3 * x^3 + 4 * x ^ 2 - 8 < 0 := by
          have h2_pos3 : (x - 1) * (x + 2) * (x ^ 2 + 2 * x + 4) < 0 := by 
            nlinarith [h2_pos, h2_pos2, sq_nonneg (x - 1), sq_nonneg (x + 2)]
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1)]
        have h2 : x^2 > 0 := by
          have hx3 : x ≠ 0 := by linarith
          exact sq_pos_of_ne_zero hx3
        apply div_neg_of_neg_of_pos
        · -- Show x^4 + 3 * x^3 + 4 * x^2 - 8 < 0
          linarith
        · -- Show x^2 > 0
          exact h2