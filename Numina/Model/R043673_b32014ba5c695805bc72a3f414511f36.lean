import Mathlib

theorem inequalities_13155 (x : ℝ) (hx : x ≠ 9 ∧ x ≠ 11) :
    20 / (x - 9) > 22 / (x - 11) ↔ x < -11 ∨ x > 9 ∧ x < 11 := by
  constructor
  · -- Assume 20 / (x - 9) > 22 / (x - 11), prove x < -11 ∨ x > 9 ∧ x < 11
    intro h
    have h1 : x - 9 ≠ 0 := by
      intro h2
      apply hx.1
      linarith
    have h2 : x - 11 ≠ 0 := by
      intro h3
      apply hx.2
      linarith
    have h3 : 20 / (x - 9) - 22 / (x - 11) > 0 := by linarith
    have h4 : (20 / (x - 9) - 22 / (x - 11)) = (-2 * (x + 11) ) / ((x - 9) * (x - 11)) := by
      field_simp [(show x - 9 ≠ 0 by assumption), (show x - 11 ≠ 0 by assumption)]
      ring
    rw [h4] at h3
    have h5 : (-2 * (x + 11) ) / ((x - 9) * (x - 11)) > 0 := h3
    apply div_pos_iff.mp at h5
    cases h5 with
    | inl h =>
      have h6 : x + 11 < 0 := by nlinarith
      left
      linarith
    | inr h =>
      have h7 : x + 11 > 0 := by nlinarith
      have h8 : 9 < x ∧ x < 11 := by
        constructor
        · -- Prove 9 < x
          nlinarith
        · -- Prove x < 11
          nlinarith
      right
      constructor
      · -- Show x > 9
        linarith
      · -- Show x < 11
        linarith
  · -- Assume x < -11 ∨ x > 9 ∧ x < 11, prove 20 / (x - 9) > 22 / (x - 11)
    rintro (h | ⟨h1, h2⟩)
    · -- Case x < -11
      have h1 : x - 9 < 0 := by linarith
      have h2 : x - 11 < 0 := by linarith
      have h3 : 20 / (x - 9) - 22 / (x - 11) > 0 := by
        have h4 : (20 / (x - 9) - 22 / (x - 11)) = (-2 * (x + 11) ) / ((x - 9) * (x - 11)) := by
          field_simp [(show x - 9 ≠ 0 by
            by_contra h9
            have : x = 9 := by linarith
            nlinarith
          ), (show x - 11 ≠ 0 by
            by_contra h11
            have : x = 11 := by linarith
            nlinarith
          )
          ]
          ring
        rw [h4]
        have h5 : (-2 * (x + 11) ) / ((x - 9) * (x - 11)) > 0 := by
          apply div_pos
          · -- Show -2 * (x + 11) > 0
            nlinarith
          · -- Show (x - 9) * (x - 11) > 0
            nlinarith
        linarith [h5]
      linarith
    · -- Case x > 9 ∧ x < 11
      have h1 : x - 9 > 0 := by linarith
      have h2 : x - 11 < 0 := by linarith
      have h3 : 20 / (x - 9) - 22 / (x - 11) > 0 := by
        have h4 : (20 / (x - 9) - 22 / (x - 11)) = (-2 * (x + 11) ) / ((x - 9) * (x - 11)) := by
          field_simp [(show x - 9 ≠ 0 by
            by_contra h9
            have : x = 9 := by linarith
            nlinarith
          ), (show x - 11 ≠ 0 by
            by_contra h11
            have : x = 11 := by linarith
            nlinarith
          )
          ]
          ring
        rw [h4]
        have h5 : (-2 * (x + 11) ) / ((x - 9) * (x - 11)) > 0 := by
          apply div_pos_of_neg_of_neg
          · -- Show -2 * (x + 11) < 0
            nlinarith
          · -- Show (x - 9) * (x - 11) < 0
            nlinarith
        linarith [h5]
      linarith