import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_324043 {f : ℝ → ℝ} (hf : f = λ x => x^2 / 10 - x / 10 + 9 / 5) :
    ∀ x, f x ≤ abs x ↔ 2 ≤ x ∧ x ≤ 9 ∨ -6 ≤ x ∧ x ≤ -3 := by
  intro x
  constructor
  · -- Assume f x ≤ |x|
    intro h
    rw [hf] at h
    by_cases h1 : x ≥ 0
    · -- If x ≥ 0, then |x| = x
      rw [abs_of_nonneg h1] at h
      have h2 : x ^ 2 / 10 - x / 10 + 9 / 5 ≤ x := by linarith [h]
      have h3 : x ^ 2 - 11 * x + 18 ≤ 0 := by
        nlinarith
      have h4 : 2 ≤ x := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 9)]
      have h5 : x ≤ 9 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 9)]
      left
      constructor
      · linarith
      · linarith
    · -- If x < 0, then |x| = -x
      rw [abs_of_neg (not_le.mp h1)] at h
      have h2 : x ^ 2 / 10 - x / 10 + 9 / 5 ≤ -x := by linarith [h]
      have h3 : x ^ 2 + 9 * x + 18 ≤ 0 := by
        nlinarith
      have h4 : -6 ≤ x := by
        nlinarith [sq_nonneg (x + 6), sq_nonneg (x + 3)]
      have h5 : x ≤ -3 := by
        nlinarith [sq_nonneg (x + 6), sq_nonneg (x + 3)]
      right
      constructor
      · linarith
      · linarith
  · -- Assume 2 ≤ x ∧ x ≤ 9 ∨ -6 ≤ x ∧ x ≤ -3, prove f x ≤ |x|
    rintro (h | h)
    · -- Case where 2 ≤ x ∧ x ≤ 9
      have h1 : x ≥ 0 := by linarith [h.1, h.2]
      rw [abs_of_nonneg h1, hf]
      have h2 : x ^ 2 / 10 - x / 10 + 9 / 5 ≤ x := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 9)]
      linarith
    · -- Case where -6 ≤ x ∧ x ≤ -3
      have h1 : x < 0 := by linarith [h.1, h.2]
      rw [abs_of_neg h1, hf]
      have h2 : x ^ 2 / 10 - x / 10 + 9 / 5 ≤ -x := by
        nlinarith [sq_nonneg (x + 6), sq_nonneg (x + 3)]
      linarith