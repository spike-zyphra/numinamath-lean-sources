import Mathlib

theorem algebra_233299 (m : ℝ) :
    ((2, 1) ∈ {p | 3 * p.2 - 2 * p.1 - m > 0} ∧
     (5, -1) ∈ {p | 3 * p.2 - 2 * p.1 - m < 0}) ↔ -13 < m ∧ m < -1 := by
  constructor
  · -- Assume ((2, 1) ∈ {p | 3 * p.2 - 2 * p.1 - m > 0} ∧ (5, -1) ∈ {p | 3 * p.2 - 2 * p.1 - m < 0}), prove -13 < m ∧ m < -1
    rintro ⟨h₁, h₂⟩
    simp at h₁ h₂
    constructor
    · linarith
    · linarith
  · -- Assume -13 < m ∧ m < -1, prove ((2, 1) ∈ {p | 3 * p.2 - 2 * p.1 - m > 0} ∧ (5, -1) ∈ {p | 3 * p.2 - 2 * p.1 - m < 0})
    rintro ⟨h₁, h₂⟩
    constructor
    · -- Show (2, 1) ∈ {p | 3 * p.2 - 2 * p.1 - m > 0}
      simp
      linarith
    · -- Show (5, -1) ∈ {p | 3 * p.2 - 2 * p.1 - m < 0}
      simp
      linarith