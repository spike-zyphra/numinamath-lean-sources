import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_209715 {x : ℝ} :
  (x^2 + x - 12 ≥ 0 ∧ |5 + x| - 2 ≠ 0 ∧ 10 - 2 * x > 0) ↔
  (x < -7 ∨ x ∈ Ioc (-7) (-4) ∨ x ∈ Ico 3 5) := by
  constructor
  · -- Assume the conditions, prove the domain
    rintro ⟨h1, h2, h3⟩
    have h4 : x ^ 2 + x - 12 ≥ 0 := h1
    have h5 : |5 + x| - 2 ≠ 0 := h2
    have h6 : 10 - 2 * x > 0 := h3
    have h7 : x < 5 := by
      linarith
    have h8 : x ≤ -4 ∨ x ≥ 3 := by
      by_contra h
      push_neg at h
      nlinarith
    have h9 : x ≠ -3 := by
      by_contra h
      have h8 : |5 + x| - 2 = 0 := by
        rw [h]
        norm_num [abs]
      contradiction
    have h10 : x ≠ -7 := by
      by_contra h
      have h11 : |5 + x| - 2 = 0 := by
        rw [h]
        norm_num [abs]
      contradiction
    rcases h8 with h11 | h11
    · -- Case where x ≤ -4
      have h13 : x ≤ -4 := h11
      have h14 : x < 5 := h7
      have h15 : x ≠ -7 := h10
      by_cases h14 : x < -7
      · -- Case x < -7
        left
        exact h14
      · -- Case -7 ≤ x ≤ -4
        have h15 : -7 < x := by
          by_contra h
          push_neg at h
          have : x = -7 := by linarith
          contradiction
        have h16 : x ≤ -4 := by linarith
        have h17 : x ∈ Ioc (-7) (-4) := by
          exact ⟨by linarith, by linarith⟩
        right
        left
        exact h17
    · -- Case x ≥ 3
      have h12 : x ≥ 3 := h11
      have h14 : x < 5 := h7
      have h18 : x ∈ Ico (3 : ℝ) (5 : ℝ) := by
        exact ⟨by linarith, by linarith⟩
      right
      right
      exact h18
  · -- Assume the domain, prove the conditions
    rintro (h1 | h2 | h3)
    · -- First alternative (x < -7)
      constructor
      · -- Show x^2 + x - 12 ≥ 0
        nlinarith
      constructor
      · -- Show |5 + x| - 2 ≠ 0
        by_contra h
        have h8 : |5 + x| = 2 := by linarith
        cases eq_or_eq_neg_of_abs_eq h8 with
        | inl h9 =>
          nlinarith
        | inr h10 =>
          nlinarith
      · -- Show 10 - 2 * x > 0
        nlinarith
    · -- Second alternative (x ∈ Ioc (-7) (-4))
      rcases h2 with ⟨h2a, h2b⟩
      constructor
      · -- Show x^2 + x - 12 ≥ 0
        nlinarith
      constructor
      · -- Show |5 + x| - 2 ≠ 0
        by_contra h
        have h8 : |5 + x| = 2 := by linarith
        cases eq_or_eq_neg_of_abs_eq h8 with
        | inl h9 =>
          nlinarith
        | inr h10 =>
          nlinarith
      · -- Show 10 - 2 * x > 0
        nlinarith
    · -- Third alternative (x ∈ Ico 3 5)
      rcases h3 with ⟨h3a, h3b⟩
      constructor
      · -- Show x^2 + x - 12 ≥ 0
        nlinarith
      constructor
      · -- Show |5 + x| - 2 ≠ 0
        by_contra h
        have h8 : |5 + x| = 2 := by linarith
        cases eq_or_eq_neg_of_abs_eq h8 with
        | inl h9 =>
          nlinarith
        | inr h10 =>
          nlinarith
      · -- Show 10 - 2 * x > 0
        nlinarith