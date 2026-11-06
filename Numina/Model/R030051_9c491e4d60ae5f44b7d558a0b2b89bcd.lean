import Mathlib

theorem inequalities_187223 (x : ℝ) (hx : x ≠ 3) :
    (5 * x + 1) / (x - 3) ≤ 1 / 3 ↔ x ∈ Set.Ico (-3 / 7) 3 := by
  simp only [Set.mem_Ico]
  constructor
  · -- Forward implication
    intro h
    have h1 : (5 * x + 1) / (x - 3) ≤ 1 / 3 := h
    have h2 : (5 * x + 1) / (x - 3) - 1 / 3 ≤ 0 := by linarith
    have h3 : (5 * x + 1) / (x - 3) - 1 / 3 = (14 * x + 6) / (3 * (x - 3)) := by 
      field_simp [(show (x - 3 : ℝ) ≠ 0 by 
        intro h'
        apply hx
        linarith
      )]
      ring
    rw [h3] at h2
    have h4 : (14 * x + 6) / (3 * (x - 3)) ≤ 0 := by 
      linarith 
    have h5 : ((14 * x + 6 ≥ 0) ∧ (x - 3 < 0)) ∨ ((14 * x + 6 ≤ 0) ∧ (x - 3 > 0)) := by
      apply div_nonpos_iff.mp at h4
      cases h4 with
      | inl h6 =>
        left
        constructor
        · -- Show 14 * x + 6 ≥ 0
          linarith
        · -- Show x - 3 < 0
          by_contra h7
          push_neg at h7
          have h8 : x - 3 ≥ 0 := by linarith
          have h9 : 3 * (x - 3) ≥ 0 := by nlinarith
          have h10 : 3 * (x - 3) = 0 := by nlinarith
          have h11 : x - 3 = 0 := by nlinarith
          have h12 : x = 3 := by linarith
          tauto
      | inr h7 =>
        right
        constructor
        · -- Show 14 * x + 6 ≤ 0
          linarith
        · -- Show x - 3 > 0
          by_contra h8
          push_neg at h8
          have h8 : x - 3 ≤ 0 := by nlinarith
          have h9 : 3 * (x - 3) ≤ 0 := by nlinarith
          have h10 : 3 * (x - 3) = 0 := by nlinarith
          have h11 : x - 3 = 0 := by nlinarith
          have h12 : x = 3 := by linarith
          tauto
    cases h5 with
    | inl h6 =>
      constructor
      · -- Show -3/7 ≤ x
        linarith
      · -- Show x < 3
        linarith
    | inr h7 =>
      linarith
  · -- Backward implication
    rintro ⟨h1, h2⟩
    have h3 : (5 * x + 1) / (x - 3) - 1 / 3 ≤ 0 := by 
      have h4 : (5 * x + 1) / (x - 3) - 1 / 3 = (14 * x + 6) / (3 * (x - 3)) := by 
        field_simp [(show (x - 3 : ℝ) ≠ 0 by 
          intro h'
          apply hx
          linarith
        )]
        ring
      have h5 : (14 * x + 6) / (3 * (x - 3)) ≤ 0 := by
        have h6 : x - 3 < 0 := by linarith
        have h7 : 14 * x + 6 ≥ 0 := by linarith
        apply div_nonpos_of_nonneg_of_nonpos 
        · linarith 
        all_goals 
          nlinarith 
      linarith [h4, h5]
    linarith