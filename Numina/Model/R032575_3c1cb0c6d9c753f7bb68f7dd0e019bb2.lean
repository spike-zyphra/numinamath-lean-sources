import Mathlib

open Set Real

theorem inequalities_248096 {A B C : Set ℝ}
    (hA : A = {x | x^2 - x - 12 ≤ 0}) (hB : B = {x | (x + 1) / (x - 1) < 0})
    (hC : C = A \ B) :
    C = {x | -3 ≤ x ∧ x ≤ -1 ∨ 1 ≤ x ∧ x ≤ 4} := by
  ext x
  simp only [hC, hA, hB, Set.mem_diff, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h: x in C, prove x in { -3 ≤ x ∧ x ≤ -1 ∨ 1 ≤ x ∧ x ≤ 4 }
    intro h
    rcases h with ⟨hA, hB⟩
    have h1 : -3 ≤ x := by
      nlinarith
    have h2 : x ≤ 4 := by
      nlinarith
    by_cases h3 : x ≤ -1
    · -- Assume x ≤ -1
      left
      constructor
      · -- Show -3 ≤ x
        linarith
      · -- Show x ≤ -1
        linarith
    · -- Assume x > -1
      have h4 : -1 < x := by
        by_contra h5
        push_neg at h5
        have h5 : x ≤ -1 := by nlinarith
        linarith
      by_cases h5 : x ≥ 1
      · -- Assume x ≥ 1
        right
        constructor
        · -- Show 1 ≤ x
          linarith
        · -- Show x ≤ 4
          nlinarith
      · -- Assume x < 1
        have h6 : x < 1 := by
          by_contra h7
          push_neg at h7
          have h7 : x ≥ 1 := by nlinarith
          linarith
        -- x in (-1, 1)
        -- b B implies not - contradiction
        have h7 : (x + 1) / (x - 1) < 0 := by
          apply div_neg_of_pos_of_neg
          · -- Show numerator is positive
            nlinarith
          · -- Show denominator is negative
            nlinarith
        linarith -- contradiction
  · -- Assume h: x in { -3 ≤ x ∧ x ≤ -1 ∨ 1 ≤ x ∧ x ≤ 4 }
    intro h
    rcases h with (h1 | h2)
    · -- Assume -3 ≤ x ∧ x ≤ -1
      rcases h1 with ⟨h3, h4⟩
      constructor
      · -- Show x^2 - x - 12 ≤ 0
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 4)]
      · -- Show ¬( (x + 1) / (x - 1) < 0 )
        have h5 : (x + 1) / (x - 1) ≥ 0 := by
          apply div_nonneg_of_nonpos
          · -- Show numerator ≤ 0
            nlinarith
          · -- Show denominator ≤ 0
            nlinarith
        linarith
    · -- Assume 1 ≤ x ∧ x ≤ 4
      rcases h2 with ⟨h3, h4⟩
      constructor
      · -- Show x^2 - x - 12 ≤ 0
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 4)]
      · -- Show ¬( (x + 1) / (x - 1) < 0 )
        have h6 : (x + 1) / (x - 1) ≥ 0 := by
          by_cases h6 : x - 1 = 0
          · -- Assume x - 1 = 0, so x = 1
            have h6 : x = 1 := by linarith
            rw [h6]
            norm_num
          · -- Assume x - 1 ≠ 0
            apply div_nonneg
            · -- Show numerator ≥ 0
              nlinarith
            · -- Show denominator ≥ 0
              by_contra h8
              push_neg at h8
              have h8 : x - 1 < 0 := by nlinarith
              have h9 : x < 1 := by nlinarith
              linarith
        linarith