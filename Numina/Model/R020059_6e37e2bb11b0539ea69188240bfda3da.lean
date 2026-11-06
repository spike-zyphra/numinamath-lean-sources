import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190109 (x : ℝ) :
  (15 / (4 + 3 * x - x ^ 2) > 1 ↔ x ∈ Ioo (-1) 4) := by
  constructor
  · -- Assume 15 / (4 + 3 * x - x ^ 2) > 1, prove x ∈ Ioo (-1) 4
    intro h
    have h1 : 4 + 3 * x - x^2 > 0 := by
      by_contra h'
      push_neg at h'
      have h2 : 4 + 3 * x - x^2 ≤ 0 := by linarith
      by_cases h3 : 4 + 3 * x - x^2 = 0
      · -- Case where 4 + 3 * x - x^2 = 0
        have h4 : 15 / (4 + 3 * x - x^2) = 0 := by
          rw [h3]
          norm_num
        linarith -- This yields a contradiction
      · -- Case where 4 + 3 * x - x^2 < 0
        have h5 : 4 + 3 * x - x^2 < 0 := by
          by_contra h6
          push_neg at h6
          have : 4 + 3 * x - x^2 = 0 := by linarith
          tauto -- This is a contradiction with h3
        have h7 : 15 / (4 + 3 * x - x^2) ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · -- Show 15 ≥ 0
            norm_num
          · -- Show 4 + 3 * x - x^2 ≤ 0
            nlinarith
        linarith -- This yields a contradiction
    have h2 : -1 < x := by
      nlinarith
    have h3 : x < 4 := by
      nlinarith
    constructor
    · -- Show -1 < x
      linarith
    · -- Show x < 4
      linarith
  · -- Assume x ∈ Ioo (-1) 4, prove 15 / (4 + 3 * x - x^2) > 1
    rintro ⟨h1, h2⟩
    have h3 : 4 + 3 * x - x^2 > 0 := by
      nlinarith
    have h4 : 15 / (4 + 3 * x - x^2) - 1 > 0 := by
      have h6 : 15 / (4 + 3 * x - x^2) - 1 = (15 - (4 + 3 * x - x^2)) / (4 + 3 * x - x^2) := by
        field_simp
        <;> ring
      rw [h6]
      apply div_pos
      · -- Show 15 - (4 + 3 * x - x^2) > 0
        nlinarith [sq_nonneg (x - 3 / 2)]
      · -- Show 4 + 3 * x - x^2 > 0
        linarith
    linarith