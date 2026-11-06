import Mathlib

theorem algebra_15138 (x : ℝ) (hx : x ≠ 1) :
    abs ((2 * x - 1) / (x - 1)) > 2 ↔ (3 / 4 < x ∧ x < 1) ∨ (x > 1) := by
  constructor
  · -- Forward implication: | (2 * x - 1) / (x - 1) | > 2 implies (3/4 < x ∧ x < 1) ∨ (x > 1)
    intro h
    have h1 : abs ((2 * x - 1) / (x - 1)) > 2 := h
    have h2 : ((2 * x - 1) / (x - 1) > 2) ∨ ((2 * x - 1) / (x - 1) < -2) := by
      by_contra h
      push_neg at h
      have h3 : abs ((2 * x - 1) / (x - 1)) ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    rcases h2 with h2 | h2
    · -- Case where (2 * x - 1) / (x - 1) > 2
      by_cases h3 : x - 1 > 0
      · -- When x - 1 > 0, so x > 1
        have h4 : x > 1 := by
          nlinarith
        right
        linarith
      · -- Case where x - 1 ≤ 0
        have h4 : x - 1 < 0 := by
          by_contra h4
          push_neg at h4
          have h5 : x - 1 = 0 := by
            linarith
          have h6 : x = 1 := by linarith
          exfalso
          apply hx
          linarith
        -- x < 1
        -- Contradiction with (2 * x - 1) / (x - 1) > 2
        have h5 : x < 1 := by
          nlinarith
        have h6 : (2 * x - 1) / (x - 1) ≤ (2 : ℝ) := by
          apply (div_le_iff_of_neg' h4).mpr
          nlinarith
        linarith
    · -- Case where (2 * x - 1) / (x - 1) < -2
      by_cases h3 : x - 1 > 0
      · -- When x - 1 > 0, so x > 1
        -- Contradiction with (2 * x - 1) / (x - 1) < -2
        have h4 : x > 1 := by
          nlinarith
        have h7 : (2 * x - 1) / (x - 1) ≥ (-2 : ℝ) := by
          apply (le_div_iff₀ h3).mpr
          nlinarith
        linarith
      · -- Case where x - 1 ≤ 0
        have h4 : x - 1 < 0 := by
          by_contra h4
          push_neg at h4
          have h5 : x - 1 = 0 := by
            linarith
          have h6 : x = 1 := by linarith
          exfalso
          apply hx
          linarith
        have h5 : x < 1 := by
          nlinarith
        have h7 : 3 / 4 < x := by
          have h5 : x - 1 < 0 := h4
          have h4 : (2 * x - 1) / (x - 1) < (-2 : ℝ) := h2
          apply (div_lt_iff_of_neg' h5).mp at h4
          nlinarith
        left
        constructor
        · -- Show 3/4 < x
          linarith
        · -- Show x < 1
          linarith
  · -- Backward implication: (3/4 < x ∧ x < 1) ∨ (x > 1) implies | (2 * x - 1) / (x - 1) | > 2
    rintro (h | h)
    · -- Case where (3/4 < x ∧ x < 1)
      have h1 : 3 / 4 < x := h.1
      have h2 : x < 1 := h.2
      have h3 : x - 1 < 0 := by
        nlinarith
      have h4 : (2 * x - 1) / (x - 1) < (-2 : ℝ) := by
        apply (div_lt_iff_of_neg' h3).mpr
        nlinarith
      rw [abs_of_neg (by
        have h4' : (2 * x - 1) / (x - 1) < 0 := by
          nlinarith
        linarith
      )]
      linarith
    · -- Case where (x > 1)
      have h1 : x > 1 := h
      have h3 : x - 1 > 0 := by
        nlinarith
      have h4 : (2 * x - 1) / (x - 1) > (2 : ℝ) := by
        apply (lt_div_iff₀ h3).mpr
        nlinarith
      rw [abs_of_pos (by
        apply div_pos
        · -- Show 2 * x - 1 > 0
          nlinarith
        all_goals
          nlinarith
      )]
      linarith