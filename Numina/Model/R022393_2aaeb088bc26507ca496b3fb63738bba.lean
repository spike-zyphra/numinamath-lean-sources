import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189948 (x : ℝ) :
  (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0 ↔
  x ∈ Iio (3 / 4) ∪ Ioi 4 ∧ x < 7 := by
  constructor
  · -- Assume (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0, prove x ∈ Iio (3 / 4) ∪ Ioi 4 ∧ x < 7
    intro h
    have h1 : 4 * x ^ 2 - 19 * x + 12 ≥ 0 := by
      by_contra h1
      push_neg at h1
      have h2 : sqrt (4 * x ^ 2 - 19 * x + 12) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
        all_goals nlinarith
      rw [h2] at h
      norm_num at h
    have h2 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
      by_contra h2
      push_neg at h2
      have h3 : sqrt (4 * x ^ 2 - 19 * x + 12) = 0 := by
        linarith [Real.sqrt_nonneg (4 * x ^ 2 - 19 * x + 12), h2]
      have h4 : 4 * x ^ 2 - 19 * x + 12 = 0 := by
        calc
          4 * x ^ 2 - 19 * x + 12 = (sqrt (4 * x ^ 2 - 19 * x + 12)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = (0 : ℝ) ^ 2 := by
            rw [h3]
          _ = (0 : ℝ) := by
            norm_num
      rw [h3] at h
      norm_num [h4] at h
    have h3 : x - 7 < 0 := by
      have h2' : sqrt (4 * x ^ 2 - 19 * x + 12) > (0 : ℝ) := h2
      apply (div_neg_iff).mp at h
      cases h with
      | inl h1 =>
        linarith
      | inr h2 =>
        linarith
    have h4 : x < 7 := by linarith
    have h5 : x ∈ Iio (3 / 4) ∪ Ioi 4 := by
      by_cases h6 : x < (3 / 4 : ℝ)
      · left
        exact h6
      · -- So x ≥ 3/4
        have h7 : x ≥ (3 / 4 : ℝ) := by linarith
        by_cases h8 : x > (4 : ℝ)
        · right
          exact h8
        · -- x ≤ 4
          have h9 : x ≤ (4 : ℝ) := by linarith
          nlinarith [sq_nonneg (x - 3 / 4), sq_nonneg (x - 4), Real.sqrt_nonneg (4 * x ^ 2 - 19 * x + 12), Real.sq_sqrt (show 0 ≤ (4 * x ^ 2 - 19 * x + 12 : ℝ) by linarith)]
    constructor
    · exact h5
    · exact h4
  · -- Assume x ∈ Iio (3 / 4) ∪ Ioi 4 ∧ x < 7, prove (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0
    rintro ⟨h1, h2⟩
    have h1' : x ∈ Iio (3 / 4) ∪ Ioi 4 := h1
    rcases h1' with (h1' | h1')
    · -- Case x < 3/4
      have h3 : x < (3 / 4 : ℝ) := h1'
      have h4 : 4 * x ^ 2 - 19 * x + 12 > 0 := by
        nlinarith [sq_pos_of_pos (show (3 / 4 - x : ℝ) > 0 by linarith), sq_nonneg (x - 4), sq_nonneg (x - 3 / 4)]
      have h5 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h6 : x - 7 < 0 := by linarith
      apply div_neg_of_neg_of_pos
      · -- Show x - 7 < 0
        linarith
      · -- Show sqrt (4 * x ^ 2 - 19 * x + 12) > 0
        exact h5
    · -- Case x > 4
      have h3 : x > (4 : ℝ) := by
        simpa using h1'
      have h4 : 4 * x ^ 2 - 19 * x + 12 > 0 := by
        nlinarith [sq_pos_of_pos (show (x - 4 : ℝ) > 0 by linarith), sq_nonneg (x - 3 / 4), sq_nonneg (x - 4)]
      have h5 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h6 : x - 7 < 0 := by linarith
      apply div_neg_of_neg_of_pos
      · -- Show x - 7 < 0
        linarith
      · -- Show sqrt (4 * x ^ 2 - 19 * x + 12) > 0
        exact h5