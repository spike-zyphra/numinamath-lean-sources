import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_188132 (x : ℝ) :
  (3 - x) / (2 * x + 1) < -3 / 4 ↔ (-15 / 2 < x ∧ x < -1 / 2) := by
  constructor
  · -- Assume (3 - x) / (2 * x + 1) < -3 / 4, prove (-15 / 2 < x ∧ x < -1 / 2)
    intro h
    have h1 : (2 * x + 1) ≠ 0 := by
      by_contra h1
      have h1' : (2 * x + 1) = 0 := by linarith
      have h2 : x = -1 / 2 := by linarith
      rw [h2] at h
      norm_num at h
    by_cases h2 : (2 * x + 1) > 0
    · -- If 2x+1 > 0, then x > -1/2
      have h3 : (2 * x + 1) > 0 := h2
      have h4 : (3 - x) / (2 * x + 1) < -3 / 4 := h
      have h5 : (3 - x) < -3 / 4 * (2 * x + 1) := by
        have h5 : (2 * x + 1) > 0 := h3
        apply (div_lt_iff₀ h5).mp at h4
        linarith
      have h6 : x < -15 / 2 := by
        linarith
      have h7 : (2 * x + 1) < 0 := by
        linarith
      linarith
    · -- If 2x+1 ≤ 0
      by_cases h2 : (2 * x + 1) < 0
      · -- If 2x+1 < 0, then x < -1/2
        have h3 : (2 * x + 1) < 0 := h2
        have h4 : (3 - x) / (2 * x + 1) < -3 / 4 := h
        have h5 : (3 - x) > -3 / 4 * (2 * x + 1) := by
          have h5 : (2 * x + 1) < 0 := h3
          apply (div_lt_iff_of_neg' (by linarith)).mp at h4
          linarith
        have h6 : x > -15 / 2 := by
          linarith
        constructor
        · linarith
        · -- Show x < -1/2
          have h7 : x < -1 / 2 := by
            by_contra h7
            push_neg at h7
            have h8 : (2 * x + 1) ≥ 0 := by linarith
            have h9 : (2 * x + 1) < 0 := h3
            linarith
          linarith
      · -- If 2x+1 = 0
        have h3 : (2 * x + 1) = 0 := by
          linarith
        have h4 : x = -1 / 2 := by
          linarith
        rw [h4] at h
        norm_num at h
  · -- Assume (-15 / 2 < x ∧ x < -1 / 2), prove (3 - x) / (2 * x + 1) < -3 / 4
    rintro ⟨h1, h2⟩
    have h3 : (2 * x + 1) < 0 := by
      linarith
    have h4 : (3 - x) / (2 * x + 1) < -3 / 4 := by
      have h5 : (2 * x + 1) < 0 := h3
      have h6 : (3 - x) > -3 / 4 * (2 * x + 1) := by
        linarith
      have h7 : (3 - x) / (2 * x + 1) < -3 / 4 := by
        have h8 : (2 * x + 1) < 0 := h5
        apply (div_lt_iff_of_neg' (by linarith)).mpr
        linarith
      linarith
    linarith