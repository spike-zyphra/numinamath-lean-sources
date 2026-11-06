import Mathlib

open Real Set

theorem inequalities_256541 (x : ℝ) :
    x > 0 ∧ (x - 1) * (x - 2) * (x - 3) < 0 ↔ x ∈ Ioo 0 1 ∪ Ioo 2 3 := by
  constructor
  · -- Assume x > 0 and (x - 1) * (x - 2) * (x - 3) < 0, show x ∈ (0, 1) ∪ (2, 3)
    rintro ⟨hx_pos, h⟩
    by_cases h2 : x < 1
    · -- Case x < 1
      have h3 : x > 0 := hx_pos
      have h4 : x < 1 := h2
      left
      exact ⟨h3, h4⟩
    · -- Case x ≥ 1
      have h2' : x ≥ 1 := by linarith
      by_cases h3 : x < 2
      · -- Case 1 ≤ x < 2
        have h4 : x ≥ 1 := h2'
        have h5 : x < 2 := h3
        have h6 : (x - 1) * (x - 2) * (x - 3) ≥ 0 := by
          have h7 : x - 1 ≥ 0 := by linarith
          have h8 : x - 2 < 0 := by linarith
          have h9 : x - 3 < 0 := by linarith
          have h10 : (x - 2) * (x - 3) > 0 := by
            nlinarith
          nlinarith
        linarith
      · -- Case x ≥ 2
        have h4 : x ≥ 2 := by linarith
        by_cases h5 : x < 3
        · -- Case 2 ≤ x < 3
          have h6 : x > 2 := by
            by_contra h'
            push_neg at h'
            have : x ≤ 2 := by linarith
            have h7 : x - 2 ≤ 0 := by linarith
            have h6' : (x - 1) * (x - 2) * (x - 3) ≥ 0 := by
              have h8 : x - 1 > 0 := by linarith
              have h9 : x - 2 ≤ 0 := by linarith
              have h10 : x - 3 < 0 := by linarith
              have h11 : (x - 2) * (x - 3) ≥ 0 := by
                nlinarith
              nlinarith
            linarith
          have h6' : x < 3 := h5
          right
          exact ⟨h6, h6'⟩
        · -- Case x ≥ 3
          have h10 : x ≥ 3 := by linarith
          have h7 : (x - 1) * (x - 2) * (x - 3) ≥ 0 := by
            have h8 : x - 1 > 0 := by linarith
            have h9 : x - 2 > 0 := by linarith
            have h10 : x - 3 ≥ 0 := by linarith
            positivity
          linarith
  · -- Assume x ∈ (0, 1) ∪ (2, 3), show x > 0 ∧ (x - 1) * (x - 2) * (x - 3) < 0
    rintro (h | h)
    · -- Case x ∈ (0, 1)
      rcases h with ⟨hx0, hx1⟩
      constructor
      · -- Show x > 0
        linarith
      · -- Show (x - 1) * (x - 2) * (x - 3) < 0
        have h2 : x < 1 := hx1
        have h3 : x - 1 < 0 := by linarith
        have h4 : x - 2 < 0 := by linarith
        have h5 : x - 3 < 0 := by linarith
        have h6 : (x - 1) * (x - 2) * (x - 3) < 0 := by
          have h7 : (x - 1) < 0 := h3
          have h8 : (x - 2) < 0 := h4
          have h9 : (x - 3) < 0 := h5
          have h10 : (x - 2) * (x - 3) > 0 := by
            nlinarith
          nlinarith
        exact h6
    · -- Case x ∈ (2, 3)
      rcases h with ⟨hx2, hx3⟩
      constructor
      · -- Show x > 0
        linarith
      · -- Show (x - 1) * (x - 2) * (x - 3) < 0
        have h2 : x > 2 := hx2
        have h1 : x - 1 > 0 := by linarith
        have h4 : x - 2 > 0 := by linarith
        have h5 : x - 3 < 0 := by linarith
        have h6 : (x - 1) * (x - 2) * (x - 3) < 0 := by
          have h7 : (x - 1) > 0 := h1
          have h8 : (x - 2) > 0 := h4
          have h9 : (x - 3) < 0 := h5
          have h10 : (x - 1) * (x - 2) > 0 := by
            nlinarith
          nlinarith
        exact h6