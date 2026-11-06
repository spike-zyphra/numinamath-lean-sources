import Mathlib

theorem inequalities_307258 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 2) : 1 / (x + 1) > 1 / (x - 2) ↔
    -1 < x ∧ x < 2 := by
  constructor
  · -- Assume 1 / (x + 1) > 1 / (x - 2), prove -1 < x ∧ x < 2
    intro h
    have h1 : x ≠ -1 := hx.1
    have h2 : x ≠ 2 := hx.2
    have h3 : (x + 1) ≠ 0 := by
      intro h4
      apply h1
      linarith
    have h4 : (x - 2) ≠ 0 := by
      intro h5
      apply h2
      linarith
    have h5 : 1 / (x + 1) - 1 / (x - 2) > 0 := by linarith
    have h6 : 1 / (x + 1) - 1 / (x - 2) = -3 / ((x + 1) * (x - 2)) := by 
      field_simp [(show x + 1 ≠ 0 by exact h3), (show x - 2 ≠ 0 by exact h4)]
      <;> ring
    rw [h6] at h5
    have h7 : (x + 1) * (x - 2) < 0 := by
      apply div_pos_iff.mp at h5
      cases h5 with
      | inl h1 =>
        nlinarith
      | inr h2 =>
        nlinarith
    constructor
    · -- Prove -1 < x 
      nlinarith
    · -- Prove x < 2 
      nlinarith
  · -- Assume -1 < x ∧ x < 2, prove 1 / (x + 1) > 1 / (x - 2)
    rintro ⟨h1, h2⟩
    have h3 : x + 1 ≠ 0 := by linarith
    have h4 : x - 2 ≠ 0 := by linarith
    have h5 : (x + 1) * (x - 2) < 0 := by 
      nlinarith
    have h6 : 1 / (x + 1) - 1 / (x - 2) > 0 := by 
      have : 1 / (x + 1) - 1 / (x - 2) = -3 / ((x + 1) * (x - 2)) := by
        field_simp [(show x + 1 ≠ 0 by linarith), (show x - 2 ≠ 0 by linarith)]
        <;> ring
      rw [this]
      apply div_pos_of_neg_of_neg
      · -- Show -3 < 0
        norm_num
      · -- Show (x + 1) * (x - 2) < 0 
        nlinarith
    linarith