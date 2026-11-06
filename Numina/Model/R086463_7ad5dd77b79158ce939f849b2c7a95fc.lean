import Mathlib

theorem inequalities_189860 (x : ℝ) :
    (x + 1) * (3 - x) * (x - 2)^2 > 0 ↔ x ∈ Set.Ioo (-1) 2 ∪ Set.Ioo 2 3 := by
  constructor
  · -- Assume left side: (x + 1) * (3 - x) * (x - 2)^2 > 0, prove right side.
    intro h
    have h1 : x + 1 > 0 := by
      by_contra h1
      push_neg at h1
      have h2 : (x + 1) * (3 - x) * (x - 2)^2 ≤ 0 := by
        have h3 : (x + 1) ≤ 0 := by linarith
        have h4 : (3 - x) > 0 := by nlinarith
        have h5 : (x - 2)^2 ≥ 0 := by nlinarith
        have h6 : (x + 1) * (3 - x) ≤ 0 := by
          nlinarith
        have h7 : (x + 1) * (3 - x) * (x - 2)^2 ≤ 0 := by
          nlinarith [h6, h5]
        linarith
      linarith
    have h2 : 3 - x > 0 := by
      by_contra h2
      push_neg at h2
      have h3 : (3 - x) ≤ 0 := by linarith
      have h4 : (x + 1) > 0 := h1
      have h5 : (x - 2)^2 > 0 := by nlinarith
      have h6 : (x + 1) * (3 - x) ≤ 0 := by
        nlinarith
      have h7 : (x + 1) * (3 - x) * (x - 2)^2 ≤ 0 := by
        nlinarith [h6, h5]
      linarith
    have h3 : (x - 2)^2 > 0 := by nlinarith
    have h4 : x > -1 := by linarith [h1]
    have h5 : x < 3 := by linarith [h2]
    have h6 : x ≠ 2 := by
      by_contra h6
      have h7 : (x - 2)^2 = 0 := by
        rw [h6]
        nlinarith
      have h8 : (x + 1) * (3 - x) * (x - 2)^2 = 0 := by
        simp [h7]
        <;> nlinarith
      linarith
    have h7 : x < 2 ∨ x > 2 := by
      by_contra h8
      push_neg at h8
      have h9 : x = 2 := by
        linarith
      exfalso
      exact h6 (by linarith)
    rcases h7 with h7 | h7
    · -- x < 2
      have h8 : x ∈ Set.Ioo (-1) 2 := ⟨h4, h7⟩
      left
      exact h8
    · -- x > 2
      have h9 : x ∈ Set.Ioo 2 3 := ⟨h7, h5⟩
      right
      exact h9
  · -- Assume right side: x ∈ (-1, 2) ∪ (2, 3), prove left side.
    intro h
    rcases h with h | h
    · -- First case: x ∈ (-1, 2)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : 3 - x > 0 := by linarith
      have h5 : (x - 2)^2 > 0 := by nlinarith
      have h6 : (x + 1) * (3 - x) > 0 := mul_pos h3 h4
      have h7 : (x + 1) * (3 - x) * (x - 2)^2 > 0 := by
        apply mul_pos
        exact h6
        exact h5
      linarith
    · -- Second case: x ∈ (2, 3)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : 3 - x > 0 := by linarith
      have h5 : (x - 2)^2 > 0 := by nlinarith
      have h6 : (x + 1) * (3 - x) > 0 := mul_pos h3 h4
      have h7 : (x + 1) * (3 - x) * (x - 2)^2 > 0 := by
        apply mul_pos
        exact h6
        exact h5
      linarith