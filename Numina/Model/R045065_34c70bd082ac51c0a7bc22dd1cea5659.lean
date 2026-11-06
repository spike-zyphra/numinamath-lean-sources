import Mathlib

theorem algebra_13695 : {x : ℝ | 2 * x + 3 ≠ 0 ∧ 2 - (2 * x + 3)⁻¹ < 4} =
    Set.Iio (-7 / 4) ∪ Set.Ioi (-3 / 2) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume x is in the left side, prove x is in the right side
    intro h
    rcases h with ⟨hx1, hx2⟩
    by_cases h1 : (2 * x + 3) > 0
    · -- If 2x + 3 > 0, then x > -3/2
      have h2 : x > -3 / 2 := by nlinarith
      right
      linarith
    · -- If 2x + 3 ≤ 0
      have h3 : (2 * x + 3) < 0 := by
        by_contra h4
        push_neg at h4
        have h4' : 2 * x + 3 = 0 := by linarith
        contradiction
      have h4 : x < -7 / 4 := by
        have h5 : (2 * x + 3) < 0 := h3
        have h6 : (2 * x + 3)⁻¹ = 1 / (2 * x + 3) := by
          field_simp [(show 2 * x + 3 ≠ 0 by assumption)]
        rw [h6] at hx2
        have h7 : 1 / (2 * x + 3) > -2 := by linarith
        have h8 : 1 < -2 * (2 * x + 3) := by
          have h10 : (2 * x + 3) < 0 := h3
          have h11 : 1 / (2 * x + 3) > -2 := h7
          have h12 : (1 / (2 * x + 3) ) * ( (2 * x + 3) ) = 1 := by
            field_simp [(show 2 * x + 3 ≠ 0 by assumption)]
          nlinarith
        nlinarith
      left
      linarith
  · -- Assume x is in the right side, prove x is in the left side
    intro h
    cases h with
    | inl h1 =>
      constructor
      · -- Show 2 * x + 3 ≠ 0
        have h4 : x < -7 / 4 := h1
        have h5 : (2 * x + 3) < 0 := by nlinarith
        have h6 : 2 * x + 3 ≠ 0 := by nlinarith
        exact h6
      · -- Show 2 - (2 * x + 3)⁻¹ < 4
        have h4 : x < -7 / 4 := h1
        have h5 : (2 * x + 3) < 0 := by nlinarith
        have h7 : (2 * x + 3)⁻¹ = 1 / (2 * x + 3) := by
          field_simp [(show 2 * x + 3 ≠ 0 by nlinarith)]
        rw [h7]
        have h8 : 1 / (2 * x + 3) > -2 := by
          have h5 : (2 * x + 3) < 0 := h5
          have h10 : 1 < -2 * (2 * x + 3) := by nlinarith
          have h11 : (1 / (2 * x + 3) ) = 1 / (2 * x + 3) := by rfl
          apply (lt_div_iff_of_neg' (by linarith)).mpr
          nlinarith
        nlinarith
    | inr h2 =>
      constructor
      · -- Show 2 * x + 3 ≠ 0
        have h4 : x > -3 / 2 := h2
        have h5 : (2 * x + 3) > 0 := by nlinarith
        have h6 : 2 * x + 3 ≠ 0 := by nlinarith
        exact h6
      · -- Show 2 - (2 * x + 3)⁻¹ < 4
        have h4 : x > -3 / 2 := h2
        have h5 : (2 * x + 3) > 0 := by nlinarith
        have h7 : (2 * x + 3)⁻¹ = 1 / (2 * x + 3) := by
          field_simp [(show 2 * x + 3 ≠ 0 by nlinarith)]
        rw [h7]
        have h8 : 1 / (2 * x + 3) > -2 := by
          have h5 : (2 * x + 3) > 0 := h5
          have h8 : 1 / (2 * x + 3) > 0 := by
            apply div_pos
            norm_num
            linarith
          linarith
        nlinarith