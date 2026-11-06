import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_236039 (a : ℝ) :
  (∀ x ∈ Icc 1 12, x^2 + 25 + abs (x^3 - 5 * x^2) ≥ a * x) ↔ a ≤ 10 := by
  constructor
  · -- Let's prove that if the inequality holds for all x in [1,12], then a ≤ 10.
    intro h
    have h5 := h 5 (by norm_num)
    norm_num [abs] at h5
    linarith
  · -- Let's prove that if a ≤ 10, then the inequality holds for all x in [1,12].
    intro ha x hx
    rcases hx with ⟨hx1, hx2⟩
    have h10 : x ^ 2 + 25 + abs (x ^ 3 - 5 * x ^ 2) ≥ 10 * x := by
      by_cases h2 : x ^ 3 - 5 * x ^ 2 ≥ 0
      · -- Case 1: x^3 - 5x^2 ≥ 0, so x ≥ 5
        have h2' : abs (x ^ 3 - 5 * x ^ 2) = x ^ 3 - 5 * x ^ 2 := by
          rw [abs_of_nonneg h2]
        rw [h2']
        nlinarith [sq_nonneg (x ^ 2 - 5 * x), sq_nonneg (x - 5), sq_nonneg (x - 1), sq_nonneg (x - 12), sq_nonneg (x * (x - 5)), sq_nonneg ((x - 5) * (x - 5))]
      · -- Case 2: x^3 - 5x^2 < 0, so x < 5
        have h2' : abs (x ^ 3 - 5 * x ^ 2) = 5 * x ^ 2 - x ^ 3 := by
          rw [abs_of_neg (by nlinarith)]
          all_goals linarith
        rw [h2']
        nlinarith [sq_nonneg (x ^ 2 - 5 * x), sq_nonneg (x - 5), sq_nonneg (x - 1), sq_nonneg (x - 12), sq_nonneg (x * (x - 5)), sq_nonneg ((x - 5) * (x - 5))]
    have h2 : a ≤ 10 := by linarith
    have h3 : a * x ≤ 10 * x := by
      have : x ≥ 0 := by linarith
      nlinarith
    linarith [h10, h3]