import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_123019 (x : ℝ) :
  (x + 1)^3 * (x^3 + 5 * x) < 10 * (x + 1)^2 + 8 ↔ x ∈ Ioo (-2) 1 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : -2 < x := by
      by_contra h2
      push_neg at h2
      nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 4), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 + 2 * x + 4), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x * (x + 2)), sq_nonneg ((x + 2) * (x - 1))]
    have h2 : x < 1 := by
      by_contra h3
      push_neg at h3
      nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 4), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 + 2 * x + 4), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x * (x + 2)), sq_nonneg ((x + 2) * (x - 1))]
    constructor <;> linarith
  · -- Assume right side, prove left side
    rintro ⟨h1, h2⟩
    have h3 : (x + 1) ^ 3 * (x^3 +5 * x) - (10 * (x + 1) ^ 2 + 8 ) < 0 := by
      nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x + 1), sq_nonneg ((x -1)), sq_nonneg ((x +2) * (x -1)), sq_nonneg ((x + 2) ^ 2 ), sq_nonneg ((x - 1) ^ 2 ), sq_nonneg (x^2 - 1), sq_nonneg (x^2 -4), sq_nonneg ((x + 1) ^2 ), sq_nonneg ((x) ^2 ), mul_pos (show 0 < (x + 2) by linarith ) (show 0 < (1 - x) by linarith ) ]
    linarith [h3]