import Mathlib

open Set Real

theorem algebra_327962 {M1 M2 : Set ℝ}
    (hM1 : M1 = {x | (x + 2) * (x - 1) > 0})
    (hM2 : M2 = {x | (x - 2) * (x + 1) > 0}) :
    M1 ∪ M2 = {x | (x ^ 2 + 4) * (x ^ 2 - 1) > 0} := by

  ext x
  simp [hM1, hM2]
  constructor
  · -- Assume x ∈ M1 ∪ M2
    rintro (h | h)
    · -- Case x ∈ M1
      have h1 : (x + 2) * (x - 1) > 0 := h
      have h2 : x ^ 2 - 1 > 0 := by
        by_contra h2
        push_neg at h2
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), 
                  sq_nonneg (x + 1), sq_nonneg (x - 2)]
      have h3 : (x ^ 2 + 4) * (x ^ 2 - 1) > 0 := by
        nlinarith [h2, sq_nonneg (x ^ 2 - 1)]
      linarith
    · -- Case x ∈ M2
      have h2 : (x - 2) * (x + 1) > 0 := h
      have h1 : x ^ 2 - 1 > 0 := by
        by_contra h1
        push_neg at h1
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), 
                  sq_nonneg (x + 2), sq_nonneg (x - 1)]
      have h3 : (x ^ 2 + 4) * (x ^ 2 - 1) > 0 := by
        nlinarith [h1, sq_nonneg (x ^ 2 - 1)]
      linarith
  · -- Assume x ∈ {x | (x ^ 2 + 4) * (x ^ 2 - 1) > 0}, prove x ∈ M1 ∪ M2
    intro h
    have h1 : x ^ 2 - 1 > 0 := by
      nlinarith [show x ^ 2 + 4 > 0 by nlinarith [sq_nonneg x], sq_nonneg (x ^ 2 - 1)]
    have h2 : x < (-1) ∨ x > 1 := by
      by_contra h2
      push_neg at h2
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
    rcases h2 with (h3 | h4)
    · -- Case x < -1
      have h3 : (x - 2) * (x + 1) > 0 := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2)]
      right
      linarith
    · -- Case x > 1
      have h4 : (x + 2) * (x - 1) > 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2)]
      left
      linarith