import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_171437 {x : ℝ} (hx : x ≠ -1) :
    x + 2 / (x + 1) > 2 ↔ x ∈ Ioi 1 ∪ Ioo (-1) 0 := by
  constructor
  · -- Assume h, prove the goal
    intro h
    have h1 : x + 2 / (x + 1) - 2 > 0 := by linarith
    have h2 : x + 2 / (x + 1) - 2 = (x * (x - 1)) / (x + 1) := by
      have h3 : x + 1 ≠ 0 := by
        intro h4
        apply hx
        linarith
      field_simp [h3]
      ring
    rw [h2] at h1
    have h3 : (x * (x - 1)) / (x + 1) > 0 := h1
    have h4 : x + 1 ≠ 0 := by
      intro h5
      apply hx
      linarith
    apply div_pos_iff.mp at h3
    cases h3 with
    | inl h5 =>
      -- Case where both numerator and denominator are positive
      rcases h5 with ⟨h6, h7⟩
      by_cases h8 : x > 1
      · -- Case x > 1
        left
        exact h8
      · -- Case x ≤ 1
        have h9 : -1 < x := by
          linarith
        have h10 : x < 0 := by
          nlinarith
        right
        exact ⟨by linarith, by linarith⟩
    | inr h5 =>
      -- Case where both numerator and denominator are negative
      rcases h5 with ⟨h6, h7⟩
      -- This side is impossible as x + 1 <0 while x >0
      nlinarith
  · -- Assume x ∈ Ioi 1 ∪ Ioo (-1) 0, show x + 2/(x + 1) > 2
    intro h
    rcases h with (h1 | h2)
    · -- Case x ∈ Ioi 1, i.e., x > 1
      have h3 : x > 1 := h1
      have h4 : x + 1 > 0 := by linarith
      have h5 : x * (x - 1) > 0 := by
        nlinarith
      have h6 : (x * (x - 1)) / (x + 1) > 0 := by
        apply div_pos
        all_goals
          nlinarith
      have h7 : x + 2 / (x + 1) - 2 > 0 := by
        have h2 : x + 2 / (x + 1) - 2 = (x * (x - 1)) / (x + 1) := by
          have h3 : x + 1 ≠ 0 := by
            intro h4
            apply hx
            linarith
          field_simp [h3]
          ring
        rw [h2] at *
        linarith
      linarith
    · -- Case x ∈ Ioo (-1) 0, i.e., -1 < x < 0
      rcases h2 with ⟨h3, h4⟩
      have h4 : x + 1 > 0 := by
        linarith
      have h5 : x * (x - 1) > 0 := by
        nlinarith
      have h6 : (x * (x - 1)) / (x + 1) > 0 := by
        apply div_pos
        all_goals
          nlinarith
      have h7 : x + 2 / (x + 1) - 2 > 0 := by
        have h2 : x + 2 / (x + 1) - 2 = (x * (x - 1)) / (x + 1) := by
          have h3 : x + 1 ≠ 0 := by
            intro h4
            apply hx
            linarith
          field_simp [h3]
          ring
        rw [h2] at *
        linarith
      linarith