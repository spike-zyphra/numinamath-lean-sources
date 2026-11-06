import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_135231 (a : ℝ) :
  (∀ x ∈ Icc 1 12, x^2 + 25 + abs (x^3 - 5 * x^2) ≥ a * x) ↔ a ≤ 10 := by
  constructor
  · -- Proof of the forward implication: If the inequality holds for all x in [1, 12], then a ≤ 10.
    intro h
    have h5 := h 5 (by norm_num)
    norm_num [abs_of_nonneg, abs_of_nonpos] at h5
    nlinarith
  · -- Proof of the converse: If a ≤ 10, then the inequality holds for all x in [1, 12].
    intro ha x hx
    rcases hx with ⟨hx1, hx2⟩
    by_cases h : x ^ 3 - 5 * x ^ 2 ≥ 0
    · -- Case where $x^3 - 5x^2 \geq 0$, so $abs(x^3 - 5x^2) = x^3 - 5x^2$.
      rw [abs_of_nonneg h]
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x ^ 2 - 25), sq_nonneg (x ^ 2 - 5 * x), sq_nonneg (x - 2), sq_nonneg (x - 5/2), sq_nonneg (x - 1), sq_nonneg (x - 12),
        mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ 12 - x by nlinarith),
        mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 12 - x by nlinarith)]
    · -- Case where $x^3 - 5x^2 < 0$, so $abs(x^3 - 5x^2) = -(x^3 - 5x^2)$.
      rw [abs_of_neg (lt_of_not_ge h)]
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x ^ 2 - 25), sq_nonneg (x ^ 2 - 5 * x), sq_nonneg (x - 2), sq_nonneg (x - 5/2), sq_nonneg (x - 1), sq_nonneg (x - 12),
        mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ 12 - x by nlinarith),
        mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 12 - x by nlinarith)]