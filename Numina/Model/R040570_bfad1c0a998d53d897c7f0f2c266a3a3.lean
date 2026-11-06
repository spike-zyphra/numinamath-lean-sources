import Mathlib

theorem algebra_15472 :
  {x : ℝ | (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) < 3 ∧ (2 * x - 3) * (x + 4) ≠ 0} = Set.Ioo (-4) (-3) ∪ Set.Ioo (3 / 2) (5 / 2) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
  constructor
  · -- Assume (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) < 3 ∧ (2 * x - 3) * (x + 4) ≠ 0, prove x ∈ (-4, -3) ∪ (3/2, 5/2)
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 < 0 := by linarith
    have h4 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) < 0 := by
      have h5 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 = (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) := by
        field_simp [(show (2 * x - 3) * (x + 4) ≠ 0 by assumption)]
        ring
      linarith [h5, h3]
    have h7 : (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) := by
      nlinarith
    have h8 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) = ((2 * x - 5) * (x + 3)) / ((2 * x - 3) * (x + 4)) := by
      rw [show (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) by nlinarith]
    rw [h8] at h4
    by_cases h7 : (2 * x - 3) * (x + 4) > 0
    · -- If the denominator is positive, then the numerator must be negative
      have h8 : (2 * x - 5) * (x + 3) < 0 := by
        have h9 : ((2 * x - 5) * (x + 3)) / ((2 * x - 3) * (x + 4)) < 0 := h4
        apply div_neg_iff.mp at h9
        cases h9 with
        | inl h7 =>
          nlinarith
        | inr h7 =>
          nlinarith
      have h17 : -3 < x ∧ x < 5 / 2 := by
        constructor
        · -- Solve (2 * x - 5) * (x + 3) < 0
          nlinarith
        · -- Solve (2 * x - 5) * (x + 3) < 0
          nlinarith
      have h15 : x > 3 / 2 := by
        nlinarith
      right
      exact ⟨by linarith, by linarith⟩
    · -- If the denominator is not positive, it must be negative (since it's not zero)
      have h7 : (2 * x - 3) * (x + 4) < 0 := by
        by_contra h8
        push_neg at h8
        have h9 : (2 * x - 3) * (x + 4) = 0 := by
          nlinarith
        contradiction
      have h8 : (2 * x - 5) * (x + 3) > 0 := by
        have h9 : ((2 * x - 5) * (x + 3)) / ((2 * x - 3) * (x + 4)) < 0 := h4
        apply div_neg_iff.mp at h9
        cases h9 with
        | inl h7 =>
          nlinarith
        | inr h7 =>
          nlinarith
      have h14 : -4 < x := by
        nlinarith
      have h15 : x < -3 := by
        nlinarith
      left
      exact ⟨by linarith, by linarith⟩
  · -- Assume x ∈ (-4, -3) ∪ (3/2, 5/2), prove (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) < 3 ∧ (2 * x - 3) * (x + 4) ≠ 0
    rintro (h | h)
    · -- Case x ∈ (-4, -3)
      rcases h with ⟨h14, h15⟩
      constructor
      · -- Show (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) < 3
        have h3 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 < 0 := by
          have h4 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 = (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) := by
            field_simp [(show (2 * x - 3) * (x + 4) ≠ 0 by
              by_contra h
              have : (2 * x - 3) * (x + 4) = 0 := by linarith
              have h10 : (2 * x - 3) = 0 ∨ (x + 4) = 0 := by
                exact mul_eq_zero.mp this
              cases h10 with
              | inl h11 =>
                have : x = 3 / 2 := by linarith
                linarith
              | inr h12 =>
                have : x = -4 := by linarith
                linarith
            )]
            ring
          rw [h4]
          have h6 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) < 0 := by
            have h7 : (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) := by
              nlinarith
            have h8 : (2 * x - 5) * (x + 3) > 0 := by
              nlinarith
            have h9 : (2 * x - 3) * (x + 4) < 0 := by
              nlinarith
            have h10 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) = ((2 * x - 5) * (x + 3)) / ((2 * x - 3) * (x + 4)) := by
              rw [show (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) by nlinarith]
            rw [h10]
            apply div_neg_of_pos_of_neg
            · linarith
            · nlinarith
          linarith
        linarith
      · -- Show (2 * x - 3) * (x + 4) ≠ 0
        by_contra h
        have : (2 * x - 3) * (x + 4) = 0 := by linarith
        have h10 : (2 * x - 3) = 0 ∨ (x + 4) = 0 := by
          exact mul_eq_zero.mp this
        cases h10 with
        | inl h11 =>
          have : x = 3 / 2 := by linarith
          linarith
        | inr h12 =>
          have : x = -4 := by linarith
          linarith
    · -- Case x ∈ (3/2, 5/2)
      rcases h with ⟨h14, h15⟩
      constructor
      · -- Show (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) < 3
        have h3 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 < 0 := by
          have h4 : (8 * x ^ 2 + 16 * x - 51) / ((2 * x - 3) * (x + 4)) - 3 = (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) := by
            field_simp [(show (2 * x - 3) * (x + 4) ≠ 0 by
              by_contra h
              have : (2 * x - 3) * (x + 4) = 0 := by linarith
              have h10 : (2 * x - 3) = 0 ∨ (x + 4) = 0 := by
                exact mul_eq_zero.mp this
              cases h10 with
              | inl h11 =>
                have : x = 3 / 2 := by linarith
                linarith
              | inr h12 =>
                have : x = -4 := by linarith
                linarith
            )]
            ring
          rw [h4]
          have h6 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) < 0 := by
            have h7 : (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) := by
              nlinarith
            have h8 : (2 * x - 5) * (x + 3) < 0 := by
              nlinarith
            have h9 : (2 * x - 3) * (x + 4) > 0 := by
              nlinarith
            have h10 : (2 * x ^ 2 + x - 15) / ((2 * x - 3) * (x + 4)) = ((2 * x - 5) * (x + 3)) / ((2 * x - 3) * (x + 4)) := by
              rw [show (2 * x ^ 2 + x - 15) = (2 * x - 5) * (x + 3) by nlinarith]
            rw [h10]
            apply div_neg_of_neg_of_pos
            · linarith
            · nlinarith
          linarith
        linarith
      · -- Show (2 * x - 3) * (x + 4) ≠ 0
        by_contra h
        have : (2 * x - 3) * (x + 4) = 0 := by linarith
        have h10 : (2 * x - 3) = 0 ∨ (x + 4) = 0 := by
          exact mul_eq_zero.mp this
        cases h10 with
        | inl h11 =>
          have : x = 3 / 2 := by linarith
          linarith
        | inr h12 =>
          have : x = -4 := by linarith
          linarith