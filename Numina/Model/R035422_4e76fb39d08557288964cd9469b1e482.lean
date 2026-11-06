import Mathlib

theorem algebra_15818 (x : ℝ) :
    (x + 1) ≠ 0 ∧ (x + 5) ≠ 0 ∧ 1 / (x + 1) + 6 / (x + 5) ≥ 1 ↔
    x ∈ Set.Ioc (-5) (-2) ∪ Set.Ioc (-1) 3 := by
  constructor
  · -- Assume the inequality holds, prove x ∈ (-5, -2] ∪ (-1, 3]
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h4 : 1 / (x + 1) + 6 / (x + 5) - 1 ≥ 0 := by linarith
    have h5 : (1 / (x + 1) + 6 / (x + 5) - 1) = (-x^2 + x + 6) / ((x + 1) * (x + 5)) := by
      field_simp [(show x + 1 ≠ 0 by exact h1), (show x + 5 ≠ 0 by exact h2)]
      ring
    rw [h5] at h4
    have h10 : ((x + 1) * (x + 5)) > 0 ∨ ((x + 1) * (x + 5)) < 0 := by
      by_contra h
      push_neg at h
      have h_eq : (x + 1) * (x + 5) = 0 := by nlinarith
      have h_eq1 : x + 1 = 0 ∨ x + 5 = 0 := by
        cases (mul_eq_zero.mp h_eq) with
        | inl h_eq2 => left; linarith
        | inr h_eq3 => right; linarith
      cases h_eq1 with
      | inl h_eq2 =>
        exfalso
        exact h1 (by linarith)
      | inr h_eq3 =>
        exfalso
        exact h2 (by linarith)
    cases h10 with
    | inl h_pos =>
      have h11 : -(x + 2) * (x - 3) ≥ 0 := by
        have h12 : (-(x + 2) * (x - 3)) / ((x + 1) * (x + 5)) ≥ 0 := by
          have h8 : (-x^2 + x + 6 : ℝ) = -(x + 2) * (x - 3) := by
            nlinarith
          rw [h8] at h4
          exact h4
        have h13 : (-(x + 2) * (x - 3)) ≥ 0 := by
          have h14 : (-(x + 2) * (x - 3)) = ((-(x + 2) * (x - 3)) / ((x + 1) * (x + 5))) * ((x + 1) * (x + 5)) := by
            field_simp
          rw [h14]
          nlinarith [h12, h_pos]
        linarith
      have h14 : (x + 2) * (x - 3) ≤ 0 := by nlinarith
      have h15 : x > -1 ∨ x < -5 := by
        have h17 : (x + 1) * (x + 5) > 0 := h_pos
        by_cases h18 : x > -1
        · tauto
        · -- x ≤ -1
          have h19 : x < -5 := by
            nlinarith [show (x + 1) * (x + 5) > 0 from h_pos]
          tauto
      cases h15 with
      | inl h15 =>
        have h17 : x ≤ 3 := by nlinarith
        have h100 : x > -1 := by linarith
        right
        exact ⟨h100, h17⟩
      | inr h15 =>
        nlinarith
    | inr h_neg =>
      have h11 : -(x + 2) * (x - 3) ≤ 0 := by
        have h12 : (-(x + 2) * (x - 3)) / ((x + 1) * (x + 5)) ≥ 0 := by
          have h8 : (-x^2 + x + 6 : ℝ) = -(x + 2) * (x - 3) := by
            nlinarith
          rw [h8] at h4
          exact h4
        have h13 : (-(x + 2) * (x - 3)) ≤ 0 := by
          have h14 : (-(x + 2) * (x - 3)) = ((-(x + 2) * (x - 3)) / ((x + 1) * (x + 5))) * ((x + 1) * (x + 5)) := by
            field_simp
          rw [h14]
          nlinarith [h12, h_neg]
        linarith
      have h14 : (x + 2) * (x - 3) ≥ 0 := by nlinarith
      have h15 : -5 < x := by
        have h15 : (x + 1) * (x + 5) < 0 := by linarith
        nlinarith
      have h16 : x < -1 := by
        have h16 : (x + 1) * (x + 5) < 0 := by linarith
        nlinarith
      have h17 : x ≤ -2 := by
        nlinarith
      left
      constructor
      · exact h15
      · nlinarith
  · -- Assume x ∈ (-5, -2] ∪ (-1, 3], prove the inequality
    rintro (h | h)
    · -- x ∈ (-5, -2]
      rcases h with ⟨h10, h11⟩
      constructor
      · -- Show x + 1 ≠ 0
        by_contra h
        have : x = -1 := by linarith
        nlinarith
      constructor
      · -- Show x + 5 ≠ 0
        by_contra h
        have : x = -5 := by linarith
        nlinarith
      · -- Show 1 / (x + 1) + 6 / (x + 5) ≥ 1
        have h3 : 1 / (x + 1) + 6 / (x + 5) ≥ 1 := by
          have h100 : -5 < x := h10
          have h101 : x ≤ -2 := h11
          have h4 : (x + 1) < 0 := by nlinarith
          have h5 : (x + 5) > 0 := by nlinarith
          have h6 : 1 / (x + 1) + 6 / (x + 5) - 1 ≥ 0 := by
            have h7 : (1 / (x + 1) + 6 / (x + 5) - 1) = (-x^2 + x + 6) / ((x + 1) * (x + 5)) := by
              field_simp [(show x + 1 ≠ 0 by nlinarith), (show x + 5 ≠ 0 by nlinarith)]
              ring
            rw [h7] at *
            have h8 : (-x^2 + x + 6) ≤ 0 := by
              nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 2)]
            have h9 : (x + 1) * (x + 5) < 0 := by nlinarith
            have h12 : (-x^2 + x + 6) / ((x + 1) * (x + 5)) ≥ 0 := by
              apply div_nonneg_of_nonpos
              · linarith
              all_goals linarith
            linarith
          linarith
        tauto
    · -- x ∈ (-1, 3]
      rcases h with ⟨h10, h11⟩
      constructor
      · -- Show x + 1 ≠ 0
        by_contra h
        have : x = -1 := by linarith
        nlinarith
      constructor
      · -- Show x + 5 ≠ 0
        by_contra h
        have : x = -5 := by linarith
        nlinarith
      · -- Show 1 / (x + 1) + 6 / (x + 5) ≥ 1
        have h3 : 1 / (x + 1) + 6 / (x + 5) ≥ 1 := by
          have h100 : -1 < x := h10
          have h101 : x ≤ 3 := h11
          have h4 : (x + 1) > 0 := by nlinarith
          have h5 : (x + 5) > 0 := by nlinarith
          have h6 : 1 / (x + 1) + 6 / (x + 5) - 1 ≥ 0 := by
            have h7 : (1 / (x + 1) + 6 / (x + 5) - 1) = (-x^2 + x + 6) / ((x + 1) * (x + 5)) := by
              field_simp [(show x + 1 ≠ 0 by nlinarith), (show x + 5 ≠ 0 by nlinarith)]
              ring
            rw [h7] at *
            have h12 : (-x^2 + x + 6) ≥ 0 := by
              nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 2)]
            have h13 : (x + 1) * (x + 5) > 0 := by nlinarith
            have h14 : (-x^2 + x + 6) / ((x + 1) * (x + 5)) ≥ 0 := by
              apply div_nonneg
              all_goals linarith
            linarith
          linarith
        tauto