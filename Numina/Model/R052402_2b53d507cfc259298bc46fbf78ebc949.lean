import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_238246 (x : ℝ) :
  (x^2 > x + 2 ∧ 4 * x^2 ≤ 4 * x + 15) ↔
  (x ∈ Ico (-3 / 2) (-1) ∪ Ioc 2 (5 / 2)) := by
  constructor
  · -- Assume (x^2 > x + 2 ∧ 4 * x^2 ≤ 4 * x + 15)
    rintro ⟨h1, h2⟩
    have h3 : (x - 2) * (x + 1) > 0 := by
      nlinarith
    have h4 : 4 * x^2 - 4 * x - 15 ≤ 0 := by
      linarith
    have h5 : -(3 / 2) ≤ x := by
      nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (x + 3 / 2)]
    have h6 : x ≤ 5 / 2 := by
      nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (x + 3 / 2)]
    have h7 : x < -1 ∨ x > 2 := by
      by_cases h : x > 2
      · -- If x > 2, then it's already covered.
        right
        exact h
      · -- If not x > 2, then x ≤ 2 and (x - 2)(x + 1) > 0 implies x < -1
        have h8 : x ≤ 2 := by linarith
        have h9 : (x - 2) * (x + 1) > 0 := h3
        have h10 : x + 1 < 0 := by
          nlinarith
        have h11 : x < -1 := by linarith
        left
        exact h11
    rcases h7 with h7 | h7
    · -- x < -1, with h5: -3/2 ≤ x
      have h8 : -3 / 2 ≤ x := by linarith
      have h9 : x < -1 := h7
      left
      exact ⟨h8, h9⟩
    · -- x > 2
      have h8 : 2 < x := h7
      have h9 : x ≤ 5 / 2 := h6
      right
      exact ⟨h8, h9⟩
  · -- Assume (x ∈ Ico (-3 / 2) (-1) ∪ Ioc 2 (5 / 2))
    rintro (h | h)
    · -- Case x ∈ [-3/2, -1)
      rcases h with ⟨h1, h2⟩
      constructor
      · -- x^2 > x + 2
        nlinarith
      · -- 4 * x^2 ≤ 4 * x + 15
        nlinarith
    · -- Case x ∈ (2, 5/2]
      rcases h with ⟨h1, h2⟩
      constructor
      · -- x^2 > x + 2
        nlinarith
      · -- 4 * x^2 ≤ 4 * x + 15
        nlinarith