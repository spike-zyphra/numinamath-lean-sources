import Mathlib

theorem algebra_178864 (x : ℝ) :
    (2 * x - 3 ≠ 0) ∧ (0 < (4 * x - 4) / (2 * x - 3) ∧ (4 * x - 4) / (2 * x - 3) < 1) ↔
    (1 / 2 < x ∧ x < 1) := by
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨h1, ⟨h2, h3⟩⟩
    by_cases h5 : (2 * x - 3) > 0
    · -- Contradiction
      have h6 : 4 * x - 4 > 0 := by
        apply div_pos_iff.mp at h2
        cases h2 with
        | inl h8 =>
          linarith
        | inr h9 =>
          linarith
      have h7 : 4 * x - 4 < (2 * x - 3) := by
        have h8 : (4 * x - 4) / (2 * x - 3) < (1 : ℝ) := h3
        apply (div_lt_iff (by linarith)).mp at h8
        linarith
      linarith
    · -- Case where 2x - 3 ≤ 0
      have h8 : (2 * x - 3) < 0 := by
        by_contra h9
        push_neg at h9
        have : (2 * x - 3) = 0 := by linarith [h9, h5]
        contradiction
      have h6 : (4 * x - 4) / (2 * x - 3) > (0 : ℝ) := h2
      apply div_pos_iff.mp at h6
      cases h6 with
      | inl h8 =>
        exfalso
        linarith [h8, h8]
      | inr h9 =>
        have h12 : 4 * x - 4 > 2 * x - 3 := by
          have h7 : (4 * x - 4) / (2 * x - 3) < (1 : ℝ) := h3
          apply (div_lt_iff_of_neg (by linarith)).mp at h7
          linarith
        constructor
        · nlinarith [h9]
        · nlinarith [h9]
  · -- Backward direction
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that 2 * x - 3 ≠ 0
      have h3 : 2 * x - 3 < 0 := by
        nlinarith
      exact by
        by_contra h
        have : 2 * x - 3 = 0 := by linarith
        nlinarith
    constructor
    · -- Show that 0 < (4 * x - 4) / (2 * x - 3)
      have h3 : 2 * x - 3 < 0 := by
        nlinarith
      have h4 : 4 * x - 4 < 0 := by
        nlinarith
      apply div_pos_of_neg_of_neg
      · linarith
      · linarith
    · -- Show that (4 * x - 4) / (2 * x - 3) < 1
      have h3 : 2 * x - 3 < 0 := by
        nlinarith
      have h4 : 4 * x - 4 < 0 := by
        nlinarith
      apply (div_lt_iff_of_neg (by linarith)).mpr
      nlinarith