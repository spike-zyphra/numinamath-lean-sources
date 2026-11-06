import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_160833 (x : ℝ) :
  (x^2 + 3 * x + 3)^(5 * x^3 - 3 * x^2) ≤
  (x^2 + 3 * x + 3)^(3 * x^3 + 5 * x) ↔
  x ≤ -2 ∨ x = -1 ∨ x ∈ Icc 0 (5 / 2) := by
  constructor
  · -- Assume the inequality holds, prove the disjunction.
    intro h
    have h1 : x ^ 2 + 3 * x + 3 > 0 := by
      nlinarith [sq_nonneg (x + 3 / 2)]
    by_cases h2 : x ^ 2 + 3 * x + 3 > 1
    · -- Case where base > 1. Then the exponents must be ordered.
      have h3 : 5 * x ^ 3 - 3 * x ^ 2 ≤ 3 * x ^ 3 + 5 * x := by
        have h4 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) ≤ (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := h
        have h5 : (5 * x ^ 3 - 3 * x ^ 2 : ℝ) ≤ (3 * x ^ 3 + 5 * x : ℝ) := by
          by_contra h6
          push_neg at h6
          have h7 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) > (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
            have h8 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) > (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt
              all_goals linarith
            linarith
          linarith
        linarith
      by_cases h4 : x ≤ -1
      · -- x ≤ -1
        have h5 : x < -1 := by
          by_contra h6
          push_neg at h6
          have h7 : x ≤ -1 := by linarith
          have h8 : x ^ 2 + 3 * x + 3 ≤ (1 : ℝ) := by
            nlinarith
          nlinarith
        have h6 : x ≤ -2 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 2)]
        left
        linarith
      · -- x > -1
        have h5 : x ≥ 0 := by nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 5 / 2), sq_nonneg (x + 1)]
        have h6 : x ≤ 5 / 2 := by nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (x), sq_nonneg (x + 1)]
        right
        right
        exact ⟨by linarith, by linarith⟩
    · -- Case where base ≤ 1.
      have h2' : x ^ 2 + 3 * x + 3 ≤ 1 := by linarith
      by_cases h2 : x ^ 2 + 3 * x + 3 < (1 : ℝ)
      · -- Case where base < 1. Then the inequality is equivalent to $5x^3-3x^2 >=3x^3+5x$.
        have h3 : 5 * x ^ 3 - 3 * x ^ 2 ≥ 3 * x ^ 3 + 5 * x := by
          have h4 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) ≤ (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := h
          have h5 : (5 * x^3 - 3 * x ^2 : ℝ) ≥ (3 * x ^3 + 5 * x : ℝ) := by
            by_contra h6
            push_neg at h6
            have h7 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) > (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
              have h8 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) > (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
                apply Real.rpow_lt_rpow_of_exponent_gt
                all_goals linarith
              linarith
            linarith
          linarith
        nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 5 / 2), sq_nonneg (x + 1)]
      · -- Case where base = 1. The points x = -1, -2.
        have h2 : x ^ 2 + 3 * x + 3 = 1 := by nlinarith
        have h3 : x = -1 ∨ x = -2 := by
          have : x ^2 + 3 * x + 3 = 1 := h2
          have : x ^ 2 + 3 * x + 2 = 0 := by linarith
          have : (x + 1) * (x + 2) = 0 := by nlinarith
          cases' (mul_eq_zero.mp this) with h4 h5
          · -- x + 1 = 0
            left
            linarith
          · -- x + 2 = 0
            right
            nlinarith
        cases h3 with
        | inl h4 =>
          simp [h4]
        | inr h5 =>
          left
          linarith
  · -- Assume the disjunction holds, prove the inequality.
    rintro (h | h | h)
    · -- x ≤ -2
      have h5 : x ≤ -2 := h
      by_cases h5 : x ^ 2 + 3 * x + 3 > (1 : ℝ)
      · -- In this case, standard analysis
        have h1 : x ^ 2 + 3 * x + 3 > 1 := h5
        have h2 : 5 * x ^ 3 - 3 * x ^ 2 ≤ 3 * x ^ 3 + 5 * x := by
          nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 5 / 2), sq_nonneg (x + 1)]
        have h3 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) ≤ (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
          rw [show (5 * x ^ 3 - 3 * x ^ 2 : ℝ) = (5 * x ^ 3 - 3 * x ^ 2 : ℝ) by linarith, show (3 * x ^ 3 + 5 * x : ℝ) = (3 * x ^ 3 + 5 * x : ℝ) by linarith]
          have h4 : 5 * x ^ 3 - 3 * x ^ 2 ≤ 3 * x ^ 3 + 5 * x := h2
          have h5 : (x^2 + 3 * x + 3) ^ (5 * x^3 - 3 * x ^ 2) ≤ (x^2 + 3 * x + 3) ^ (3 * x^3 + 5 * x) := by
            apply Real.rpow_le_rpow_of_exponent_le
            all_goals nlinarith
          linarith
        linarith [h3]
      · -- Case base ≤ 1
        have h7 : x ^ 2 + 3 * x + 3 ≤ 1 := by
          nlinarith
        have h77 : x ^ 2 + 3 * x + 3 = 1 := by
          nlinarith [h7, h5]
        have h8 : (x + 1) * (x + 2) = 0 := by
          nlinarith
        have h9 : x = -1 ∨ x = -2 := by
          cases (mul_eq_zero.mp h8) with
          | inl h10 => 
            left
            linarith
          | inr h11 => 
            right
            linarith
        cases h9 with
        | inl h10 =>
          -- x = -1
          exfalso
          nlinarith
        | inr h10 =>
          rw [show x = -2 by linarith [h10]]
          norm_num
    · -- x = -1
      rw [h]
      norm_num
    · -- x ∈ [0, 5/2]
      have h1 : x ^ 2 + 3 * x + 3 > 1 := by
        have : x ^ 2 + 3 * x + 2 > 0 := by
          have h6 : x ≥ 0 := h.1
          nlinarith
        nlinarith
      have h2 : 5 * x ^ 3 - 3 * x ^ 2 ≤ 3 * x ^ 3 + 5 * x := by
        nlinarith [h.1, h.2, sq_nonneg (x - 0), sq_nonneg (x - 5 / 2), sq_nonneg (x + 1)]
      have h3 : (x ^ 2 + 3 * x + 3 : ℝ) ^ (5 * x ^ 3 - 3 * x ^ 2 : ℝ) ≤ (x ^ 2 + 3 * x + 3 : ℝ) ^ (3 * x ^ 3 + 5 * x : ℝ) := by
        rw [show (5 * x ^ 3 - 3 * x ^ 2 : ℝ) = (5 * x ^ 3 - 3 * x ^ 2 : ℝ) by linarith, show (3 * x ^ 3 + 5 * x : ℝ) = (3 * x ^ 3 + 5 * x : ℝ) by linarith]
        have h4 : 5 * x ^ 3 - 3 * x ^ 2 ≤ 3 * x ^ 3 + 5 * x := h2
        have h5 : (x^2 + 3 * x + 3) ^ (5 * x^3 - 3 * x ^ 2) ≤ (x^2 + 3 * x + 3) ^ (3 * x^3 + 5 * x) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals nlinarith
        linarith
      linarith [h3]